(function(){
"use strict";
var $=function(id){return document.getElementById(id)};
var LS={
  get:function(k){try{return localStorage.getItem(k)}catch(e){return null}},
  set:function(k,v){try{localStorage.setItem(k,v);return true}catch(e){return false}},
  del:function(k){try{localStorage.removeItem(k)}catch(e){}}
};
var TILE_CACHE="tcc-tiles-v1";
var DEF_TILE="https://tile.openstreetmap.org/{z}/{x}/{y}.png";
var DEF_ATTR="© OpenStreetMap contributors";

/* ================= state ================= */
var route=null;
var cps=[
  {name:"CP1",km:21,time:"08:30"},
  {name:"CP2",km:33.2,time:"12:00"},
  {name:"CP3",km:45.7,time:"15:30"},
  {name:"เส้นชัย",km:54,time:"17:30"}
];
var planStart="03:30",startTs=null,simKm=0,shiftH=0,gpsKm=null,gpsWatch=null;
var S={alertOn:true,vib:true,snd:true,lead:300,minGain:30,steep:12,offOn:true,offDist:50,tileUrl:"",tileAttr:"",base:"road",satUrl:"",satAttr:"",demUrl:"",ex:3,gName:"",gRoom:"",gOn:false,gShare:true,fbUrl:"",gView:false,gAv:0,gCu:"",exv:0};
var ownPlan=null,gpsFix=null,trail=[],offRoute=false,offFixes=0,reloc=null,lastOffAlert=0,trailSaved=0;
var events=[],climbs=[],lastKm=null,selSeg=null,scrubKm=null,hillFilter="up",follow=false;

function load(){
  var s=LS.get("tcc.state");
  if(s){try{var o=JSON.parse(s);
    if(o.cps&&o.cps.length)cps=o.cps; if(o.planStart)planStart=o.planStart;
    if(o.startTs)startTs=o.startTs; if(typeof o.simKm==="number")simKm=o.simKm; if(typeof o.shiftH==="number")shiftH=o.shiftH;
    if(o.S){for(var k in o.S){if(o.S.hasOwnProperty(k))S[k]=o.S[k]}}
  }catch(e){}}
  var r=LS.get("tcc.route");
  if(r){try{route=build(JSON.parse(r))}catch(e){route=null}}
}
function save(){LS.set("tcc.state",JSON.stringify({cps:(ownPlan?ownPlan.cps:cps),planStart:(ownPlan?ownPlan.ps:planStart),startTs:startTs,simKm:simKm,shiftH:shiftH,S:S}))}

/* ================= helpers ================= */
function pad(n){return n<10?"0"+n:""+n}
function hms(ms){var neg=ms<0;ms=Math.abs(ms);var s=Math.floor(ms/1000),h=Math.floor(s/3600),m=Math.floor(s%3600/60);return (neg?"-":"")+h+":"+pad(m)+":"+pad(s%60)}
function hhmm(ts){var d=new Date(ts);return pad(d.getHours())+":"+pad(d.getMinutes())}
function toMin(t){var a=(t||"0:0").split(":");return (+a[0])*60+(+a[1]||0)}
function offsetMs(cp){return ((toMin(cp.time)-toMin(planStart)+1440)%1440)*60000}
function nowMs(){return Date.now()+shiftH*3600000}
function css(n){return getComputedStyle(document.documentElement).getPropertyValue(n).trim()}
function clamp(v,a,b){return v<a?a:(v>b?b:v)}
function pace(msPerKm){if(!isFinite(msPerKm)||msPerKm<=0)return "-";var s=Math.round(msPerKm/1000),m=Math.floor(s/60);return m+":"+pad(s%60)+"/กม."}
function sgn(n,d){var v=n.toFixed(d||0);return (n>0?"+":"")+v}
function runnerKm(){return gpsKm!=null?gpsKm:simKm}
function merc2lat(v){var n=Math.PI*(1-2*v);return Math.atan(Math.sinh(n))*180/Math.PI}
function idxAt(km){if(!route)return 0;return clamp(Math.round(km*1000/route.step),0,route.n)}

/* ================= grade colours ================= */
var STOPS=[[-18,[37,99,235]],[-8,[8,145,178]],[-2,[52,190,140]],[2,[190,205,150]],[6,[245,200,60]],[10,[245,140,40]],[15,[225,60,45]],[22,[170,20,50]]];
function gcRGB(g){
  if(g<=STOPS[0][0])return STOPS[0][1];
  for(var i=1;i<STOPS.length;i++){if(g<=STOPS[i][0]){var a=STOPS[i-1],b=STOPS[i],t=(g-a[0])/(b[0]-a[0]);
    return [Math.round(a[1][0]+(b[1][0]-a[1][0])*t),Math.round(a[1][1]+(b[1][1]-a[1][1])*t),Math.round(a[1][2]+(b[1][2]-a[1][2])*t)]}}
  return STOPS[STOPS.length-1][1];
}
function gc(g){var c=gcRGB(g);return "rgb("+c[0]+","+c[1]+","+c[2]+")"}

/* ================= route analysis ================= */
function hav(a,b,c,d){var R=6371000,t=Math.PI/180,dl=(c-a)*t,dn=(d-b)*t;
  var x=Math.sin(dl/2)*Math.sin(dl/2)+Math.cos(a*t)*Math.cos(c*t)*Math.sin(dn/2)*Math.sin(dn/2);
  return 2*R*Math.asin(Math.sqrt(x))}
function movavg(a,w){var n=a.length,o=new Array(n),i,s=0,lo=0,hi=-1;
  for(i=0;i<n;i++){var L=Math.max(0,i-w),H=Math.min(n-1,i+w);
    while(hi<H){hi++;s+=a[hi]}while(lo<L){s-=a[lo];lo++}o[i]=s/(H-L+1)}return o}
function build(o){
  var p=o.pts,n0=p.length,cum=[0],i;
  for(i=1;i<n0;i++)cum.push(cum[i-1]+hav(p[i-1][0],p[i-1][1],p[i][0],p[i][1]));
  var total=cum[n0-1];
  // ระยะขึ้นสะสมจากจุดดิบ
  var gain=0,ref=p[0][2],mx=-1e9;
  for(i=0;i<n0;i++){var e=p[i][2];if(e>mx)mx=e;if(e-ref>=3){gain+=e-ref;ref=e}else if(ref-e>=3){ref=e}}
  // สุ่มใหม่ทุก ~10 ม.
  var N=Math.max(2,Math.round(total/10)),step=total/N,lat=[],lon=[],ele=[],mu=[],mv=[],j=0;
  for(i=0;i<=N;i++){var d=i*step;while(j<n0-2&&cum[j+1]<d)j++;
    var seg=cum[j+1]-cum[j],t=seg>0?clamp((d-cum[j])/seg,0,1):0;
    var la=p[j][0]+(p[j+1][0]-p[j][0])*t,lo=p[j][1]+(p[j+1][1]-p[j][1])*t,el=p[j][2]+(p[j+1][2]-p[j][2])*t;
    lat.push(la);lon.push(lo);ele.push(el);
    mu.push((lo+180)/360);var r=la*Math.PI/180;mv.push((1-Math.log(Math.tan(r)+1/Math.cos(r))/Math.PI)/2)}
  var se=movavg(movavg(ele,3),3),grade=[],k=5;
  for(i=0;i<=N;i++){var a=Math.max(0,i-k),b=Math.min(N,i+k);grade.push(clamp((se[b]-se[a])/((b-a)*step)*100,-45,45))}
  var R={name:o.name||"",sample:!!o.sample,pts:p,n:N,step:step,total:total,gain:gain,max:mx,
    lat:lat,lon:lon,ele:ele,mu:mu,mv:mv,se:se,grade:grade};
  R.segs=segments(R);
  return R;
}
function segments(R){
  var e=movavg(R.se,5),M=R.n,P=15,tp=[0],dir=0,ext=0,hi=0,lo=0,i;
  function push(x){if(x>tp[tp.length-1])tp.push(x)}
  for(i=1;i<=M;i++){
    if(dir===0){
      if(e[i]>e[hi])hi=i;if(e[i]<e[lo])lo=i;
      if(e[i]-e[lo]>=P){push(lo);dir=1;ext=i}else if(e[hi]-e[i]>=P){push(hi);dir=-1;ext=i}
    }else if(dir===1){
      if(e[i]>e[ext])ext=i;else if(e[ext]-e[i]>=P){push(ext);dir=-1;ext=i}
    }else{
      if(e[i]<e[ext])ext=i;else if(e[i]-e[ext]>=P){push(ext);dir=1;ext=i}
    }
  }
  if(dir!==0)push(ext);push(M);
  var out=[];
  for(i=0;i<tp.length-1;i++){
    var a=tp[i],b=tp[i+1],g=0,l=0,mg=0,x;
    for(x=a+1;x<=b;x++){var d=R.se[x]-R.se[x-1];if(d>0)g+=d;else l-=d}
    var up=R.se[b]>=R.se[a];
    for(x=a;x<=b;x++){var gg=R.grade[x];if(up?gg>mg:gg<mg)mg=gg}
    out.push({a:a,b:b,up:up,gain:g,loss:l,len:(b-a)*R.step,avg:(R.se[b]-R.se[a])/((b-a)*R.step)*100,maxG:mg});
  }
  return out;
}
function buildEvents(){
  events=[];climbs=[];
  if(!route)return;
  var st=route.step,ups=route.segs.filter(function(s){return s.up&&s.gain>=S.minGain});
  route.segs.forEach(function(s){s.cn=0});
  ups.forEach(function(s,i){s.cn=i+1;s.ct=ups.length;climbs.push(s);
    events.push({kind:"climb",s:s,start:s.a*st/1000,end:s.b*st/1000})});
  // ช่วงชัน: ความชันเกินค่าที่ตั้ง ต่อเนื่องอย่างน้อย 100 ม.
  var g=route.grade,i=0,M=route.n,runs=[];
  while(i<=M){
    if(g[i]>=S.steep){var a=i,b=i,gap=0,j=i;
      while(j<=M&&(g[j]>=S.steep||gap<3)){if(g[j]>=S.steep){b=j;gap=0}else gap++;j++}
      if((b-a)*st>=100)runs.push([a,b]);i=Math.max(j,b+1)}
    else i++;
  }
  runs.forEach(function(r){var len=(r[1]-r[0])*st,avg=(route.se[r[1]]-route.se[r[0]])/len*100;
    events.push({kind:"pitch",a:r[0],b:r[1],avg:avg,len:len,start:r[0]*st/1000,end:r[1]*st/1000})});
  events.sort(function(x,y){return x.start-y.start});
}

/* ================= sample + GPX ================= */
function sampleRoute(){
  var N=1300,m=[],i,th;
  for(i=0;i<=N;i++){th=2*Math.PI*i/N;m.push([Math.cos(th)+0.35*Math.cos(3*th),0.7*Math.sin(th)+0.25*Math.sin(2*th)])}
  var cum=[0];for(i=1;i<=N;i++)cum.push(cum[i-1]+Math.hypot(m[i][0]-m[i-1][0],m[i][1]-m[i-1][1]));
  var L=cum[N],k=52700/L,lat0=14.0,lon0=100.0,pts=[];
  for(i=0;i<=N;i++){var f=cum[i]/L,e=420+170*Math.sin(2*Math.PI*3*f)+45*Math.sin(2*Math.PI*9*f)+40*Math.sin(2*Math.PI*6*f);
    pts.push([lat0+m[i][1]*k/111320,lon0+m[i][0]*k/(111320*Math.cos(lat0*Math.PI/180)),e])}
  return build({name:"เส้นทางตัวอย่าง (ไม่ใช่เส้นทางจริง)",sample:true,pts:pts});
}
function parseGpx(text,name){
  var doc=new DOMParser().parseFromString(text,"application/xml");
  if(doc.getElementsByTagName("parsererror").length)throw new Error("อ่านไฟล์ไม่ได้ ตรวจสอบว่าเป็นไฟล์ GPX");
  var nodes=doc.getElementsByTagName("trkpt");
  if(!nodes.length)nodes=doc.getElementsByTagName("rtept");
  if(nodes.length<2)throw new Error("ไม่พบจุดเส้นทางในไฟล์ (trkpt หรือ rtept)");
  var pts=[],lastEle=0;
  for(var i=0;i<nodes.length;i++){
    var la=parseFloat(nodes[i].getAttribute("lat")),lo=parseFloat(nodes[i].getAttribute("lon"));
    if(isNaN(la)||isNaN(lo))continue;
    var el=nodes[i].getElementsByTagName("ele")[0],ev=el?parseFloat(el.textContent):NaN;
    if(isNaN(ev))ev=lastEle;lastEle=ev;pts.push([la,lo,ev]);
  }
  if(pts.length<2)throw new Error("จุดเส้นทางไม่พอ");
  if(pts.length>6000){var out=[],st=(pts.length-1)/5999;for(var q=0;q<6000;q++)out.push(pts[Math.round(q*st)]);pts=out}
  pts=pts.map(function(q){return [Math.round(q[0]*1e6)/1e6,Math.round(q[1]*1e6)/1e6,Math.round(q[2]*10)/10]});
  return {name:name,pts:pts};
}

/* ================= canvas helpers ================= */
function setup(cv){var r=cv.getBoundingClientRect(),d=window.devicePixelRatio||1;
  cv.width=Math.max(1,Math.round(r.width*d));cv.height=Math.max(1,Math.round(r.height*d));
  var c=cv.getContext("2d");c.setTransform(d,0,0,d,0,0);return {c:c,w:r.width,h:r.height}}
var raf=0;
function reqDraw(){if(raf)return;raf=requestAnimationFrame(function(){raf=0;if(mode3d)draw3d();else drawMap()})}

/* ================= elevation profile ================= */
var pv={a:0,b:1};
function drawProfile(cv,tall){
  var s=setup(cv),c=s.c,W=s.w,H=s.h;c.clearRect(0,0,W,H);
  if(!route){c.fillStyle=css("--muted");c.font="14px "+css("--font");c.textAlign="center";c.fillText("ยังไม่มีเส้นทาง",W/2,H/2);return}
  var fz=cv.id==="prof3"||cv.id==="prof2",L=tall?42:34,R=10,T=tall?22:16,B=22,pw=W-L-R,tot=route.total,mn=1e9,mx=-1e9,i,va=0,vb=tot;
  if(fz){va=pv.a*tot;vb=pv.b*tot}
  var i0=Math.max(0,Math.floor(va/route.step)),i1=Math.min(route.n,Math.ceil(vb/route.step));
  for(i=i0;i<=i1;i++){var e=route.se[i];if(e<mn)mn=e;if(e>mx)mx=e}
  mn=Math.floor(mn/50)*50;mx=Math.ceil(mx/50)*50;if(mx<=mn)mx=mn+50;
  var Y=function(e){return T+(1-(e-mn)/(mx-mn))*(H-T-B)},X=function(m){return L+(m-va)/(vb-va)*pw};
  c.font="11px "+css("--mono");c.fillStyle=css("--muted");c.textBaseline="alphabetic";c.textAlign="right";
  c.fillText(mx,L-5,T+4);c.fillText(mn,L-5,H-B);
  c.strokeStyle=css("--line");c.lineWidth=1;c.beginPath();c.moveTo(L,H-B+.5);c.lineTo(W-R,H-B+.5);c.stroke();
  var spanKm=(vb-va)/1000,stepKm=[.1,.2,.5,1,2,5,10,20].filter(function(q){return spanKm/q<=(fz?12:8)})[0]||20;if(!fz)stepKm=tot/1000>40?10:(tot/1000>15?5:2);c.textAlign="center";
  for(var k=Math.ceil(va/1000/stepKm);k*stepKm*1000<=vb;k++){c.fillText(+(k*stepKm).toFixed(2),X(k*stepKm*1000),H-6)}
  c.save();c.beginPath();c.rect(L,0,pw+R,H-B+8);c.clip();
  // แท่งสีตามความชัน
  var sel=selSeg,cols=Math.floor(pw),bw=pw/cols,riB=idxAt(runnerKm());
  for(var x=0;x<cols;x++){
    var m0=va+x/cols*(vb-va),idx=clamp(Math.round(m0/route.step),0,route.n),top=Y(route.se[idx]);
    var inSel=!sel||(idx>=sel.a&&idx<=sel.b);
    c.globalAlpha=inSel?(idx<riB?.35:1):.28;c.fillStyle=gc(route.grade[idx]);
    c.fillRect(L+x*bw,top,bw+.6,H-B-top);
  }
  c.globalAlpha=1;
  if(tall){ // เลขทางขึ้น
    c.font="600 10px "+css("--mono");c.textAlign="center";var lastX=-99;
    climbs.forEach(function(s){var pk=s.b,x=X(pk*route.step);if(x-lastX<16)return;lastX=x;
      c.fillStyle=css("--ink");c.fillText(s.cn,x,Math.max(T-6,Y(route.se[pk])-4))});
  }
  // Cutoff
  c.font="11px "+css("--mono");c.setLineDash([3,3]);c.lineWidth=1;c.strokeStyle=css("--ink");c.fillStyle=css("--ink");c.textAlign="center";
  cps.forEach(function(cp){var x=X(Math.min(cp.km*1000,tot));c.beginPath();c.moveTo(x,T);c.lineTo(x,H-B);c.stroke();
    if(!tall)c.fillText(cp.name,clamp(x,22,W-22),T-4)});
  c.setLineDash([]);
  // ตำแหน่งเรา
  var rk=clamp(runnerKm()*1000,0,tot),rx=X(rk),ri=idxAt(runnerKm());
  c.strokeStyle=css("--ink");c.lineWidth=2;c.beginPath();c.moveTo(rx,T);c.lineTo(rx,H-B);c.stroke();
  c.beginPath();c.arc(rx,Y(route.se[ri]),5,0,6.283);c.fillStyle=css("--surface");c.fill();c.lineWidth=2.5;c.stroke();
  spriteAt(c,myAv(),rx,Y(route.se[ri])-4,tall?28:20);
  grp.friends.forEach(function(f){
    if(f.km==null)return;var fx=X(clamp(f.km*1000,0,tot)),fi=idxAt(f.km);
    c.globalAlpha=f.stale?.45:1;c.strokeStyle=f.color;c.lineWidth=1.5;c.beginPath();c.moveTo(fx,T);c.lineTo(fx,H-B);c.stroke();
    c.beginPath();c.arc(fx,Y(route.se[fi]),3.5,0,6.283);c.fillStyle=f.color;c.fill();
    spriteAt(c,f.av,fx,Y(route.se[fi])-4,tall?28:20);
    if(tall){c.font="600 10px "+css("--font");c.textAlign="center";c.lineWidth=3;c.strokeStyle=css("--surface");c.strokeText(f.name,fx,Math.max(Y(route.se[fi])-4,32)+11);c.fillStyle=css("--ink");c.fillText(f.name,fx,Math.max(Y(route.se[fi])-4,32)+11)}
    c.globalAlpha=1});
  if(tall&&scrubKm!=null){var sx=X(clamp(scrubKm*1000,0,tot));c.strokeStyle=css("--accent");c.lineWidth=1.5;c.beginPath();c.moveTo(sx,T);c.lineTo(sx,H-B);c.stroke()}
  c.restore();
}

/* ================= tile map ================= */
var MV={u:.5,v:.5,z:12,w:300,h:300};
var tileCache=new Map();
function tileUrl(z,x,y){return (S.tileUrl||DEF_TILE).replace("{z}",z).replace("{x}",x).replace("{y}",y)}
function getImg(u){
  var im=tileCache.get(u);if(im)return im;
  im=new Image();im.crossOrigin="anonymous";im.onload=reqDraw;
  im.onerror=function(){
    if(!im._noCors){ // บางแหล่งไม่ส่ง CORS: ลองโหลดแบบธรรมดา ใช้ได้เฉพาะแผนที่ 2D (3D ต้องใช้ CORS)
      var i2=new Image();i2._noCors=true;i2.onload=reqDraw;
      i2.onerror=function(){i2._dead=true;setTimeout(function(){tileCache.delete(u)},8000)};
      i2.src=u;tileCache.set(u,i2);
    }
  };
  im.src=u;tileCache.set(u,im);
  if(tileCache.size>900)tileCache.delete(tileCache.keys().next().value);
  return im;
}
function getTile(z,x,y){return getImg(baseUrl(z,x,y))}
function fitRoute(){
  if(!route)return;
  var u0=1,u1=0,v0=1,v1=0,i,cv=$("map");
  if(cv.clientWidth>0){MV.w=cv.clientWidth;MV.h=cv.clientHeight}
  for(i=0;i<=route.n;i+=3){var u=route.mu[i],v=route.mv[i];if(u<u0)u0=u;if(u>u1)u1=u;if(v<v0)v0=v;if(v>v1)v1=v}
  var du=Math.max(u1-u0,1e-6),dv=Math.max(v1-v0,1e-6);
  MV.u=(u0+u1)/2;MV.v=(v0+v1)/2;
  MV.z=clamp(Math.log(Math.min(MV.w/(du*256),MV.h/(dv*256))*.86)/Math.LN2,3,17);
}
function zoomAt(px,py,dz){
  var ws=256*Math.pow(2,MV.z),wu=MV.u+(px-MV.w/2)/ws,wv=MV.v+(py-MV.h/2)/ws;
  MV.z=clamp(MV.z+dz,3,18);var nws=256*Math.pow(2,MV.z);
  MV.u=wu-(px-MV.w/2)/nws;MV.v=clamp(wv-(py-MV.h/2)/nws,0,1);
}
function setFollow(on){follow=on;$("zFollow").setAttribute("aria-pressed",on?"true":"false");if(on)centerRunner()}
function centerRunner(){if(!route)return;var i=idxAt(runnerKm());if(gpsFix){MV.u=gpsFix.u;MV.v=gpsFix.v}else{MV.u=route.mu[i];MV.v=route.mv[i]}if(MV.z<14)MV.z=14.5;reqDraw()}

function drawMap(){
  var cv=$("map");if(cv.offsetParent===null)return;
  var s=setup(cv),c=s.c,W=s.w,H=s.h;MV.w=W;MV.h=H;
  c.fillStyle=css("--bg");c.fillRect(0,0,W,H);
  var z=MV.z,z0=Math.min(Math.floor(z),17),sc=Math.pow(2,z-z0),n=Math.pow(2,z0),ws=256*Math.pow(2,z);
  // ไทล์
  var cx=MV.u*n*256,cy=MV.v*n*256,T=256*sc,
    x0=Math.floor((cx-W/(2*sc))/256),x1=Math.floor((cx+W/(2*sc))/256),
    y0=Math.max(0,Math.floor((cy-H/(2*sc))/256)),y1=Math.min(n-1,Math.floor((cy+H/(2*sc))/256));
  if((x1-x0+1)*(y1-y0+1)<=60){
    for(var ty=y0;ty<=y1;ty++)for(var tx=x0;tx<=x1;tx++){
      var im=getTile(z0,((tx%n)+n)%n,ty);
      if(im.complete&&im.naturalWidth)c.drawImage(im,W/2+(tx*256-cx)*sc,H/2+(ty*256-cy)*sc,T+.5,T+.5);
    }
  }
  if(!route){return}
  var X=function(i){return W/2+(route.mu[i]-MV.u)*ws},Y=function(i){return H/2+(route.mv[i]-MV.v)*ws},i;
  c.lineJoin="round";c.lineCap="round";
  // เส้นขอบ
  c.beginPath();for(i=0;i<=route.n;i+=2){i?c.lineTo(X(i),Y(i)):c.moveTo(X(i),Y(i))}
  c.strokeStyle=css("--surface");c.globalAlpha=.92;c.lineWidth=12;c.stroke();c.globalAlpha=1;
  // สีตามความชัน ทุก 80 ม. ช่วงที่ผ่านแล้วเป็นสีเทาจาง วาดก่อน เพื่อให้ช่วงที่ยังไม่ผ่านอยู่ด้านบนเสมอ
  var chunk=Math.max(2,Math.round(80/route.step)),riP=idxAt(runnerKm());
  for(var pass=0;pass<2;pass++){
    for(i=0;i<route.n;i+=chunk){
      var e=Math.min(route.n,i+chunk),done=e<=riP;
      if((pass===0)!==done)continue;
      var g=(route.se[e]-route.se[i])/((e-i)*route.step)*100;
      c.beginPath();c.moveTo(X(i),Y(i));
      var q=i+Math.max(1,Math.floor(chunk/2));if(q<e)c.lineTo(X(q),Y(q));c.lineTo(X(e),Y(e));
      if(done){c.strokeStyle=css("--muted");c.globalAlpha=.55;c.lineWidth=6}else{c.strokeStyle=gc(g);c.globalAlpha=1;c.lineWidth=8}
      c.stroke();
    }
  }
  c.globalAlpha=1;
  // ลูกศรบอกทิศทางวิ่ง เฉพาะช่วงที่ยังไม่ผ่าน
  var mpp=40075016.686*Math.cos(route.lat[Math.min(riP,route.n)]*Math.PI/180)/ws,ad=Math.max(5,Math.round(70*mpp/route.step));
  for(i=Math.max(ad,Math.ceil((riP+1)/ad)*ad);i<route.n-2;i+=ad){
    var ax=X(i),ay=Y(i);if(ax<-10||ax>W+10||ay<-10||ay>H+10)continue;
    var ang=Math.atan2(Y(i+2)-ay,X(i+2)-ax);
    c.save();c.translate(ax,ay);c.rotate(ang);c.beginPath();c.moveTo(6,0);c.lineTo(-4,-4.5);c.lineTo(-4,4.5);c.closePath();
    c.fillStyle=css("--surface");c.fill();c.lineWidth=1.5;c.strokeStyle=css("--ink");c.stroke();c.restore();
  }
  // ช่วงที่เลือก
  if(selSeg){c.beginPath();for(i=selSeg.a;i<=selSeg.b;i++){i>selSeg.a?c.lineTo(X(i),Y(i)):c.moveTo(X(i),Y(i))}
    c.strokeStyle=css("--ink");c.lineWidth=2;c.stroke()}
  // CP
  c.font="600 12px "+css("--mono");c.textBaseline="middle";
  cps.forEach(function(cp){var j=idxAt(Math.min(cp.km,route.total/1000)),x=X(j),y=Y(j);
    c.beginPath();c.arc(x,y,6,0,6.283);c.fillStyle=css("--surface");c.fill();c.lineWidth=2.5;c.strokeStyle=css("--ink");c.stroke();
    var right=x>W-80;c.textAlign=right?"right":"left";
    c.lineWidth=3;c.strokeStyle=css("--surface");c.strokeText(cp.name,x+(right?-11:11),y-11);
    c.fillStyle=css("--ink");c.fillText(cp.name,x+(right?-11:11),y-11)});
  c.beginPath();c.arc(X(0),Y(0),5,0,6.283);c.fillStyle=css("--ok");c.fill();c.lineWidth=2;c.strokeStyle=css("--surface");c.stroke();
  // ตำแหน่งเรา
  var ri=idxAt(runnerKm());
  c.beginPath();c.arc(X(ri),Y(ri),13,0,6.283);c.fillStyle=css("--accent");c.globalAlpha=.25;c.fill();c.globalAlpha=1;
  if(gpsFix){c.beginPath();c.arc(X(ri),Y(ri),7,0,6.283);c.fillStyle=css("--accent");c.fill();c.lineWidth=2.5;c.strokeStyle=css("--surface");c.stroke()}else ownMarker(c,X(ri),Y(ri));
  // รอยทางที่เดินจริง
  if(trail.length>1){
    var tcol=(grp.on&&!S.gView&&grp.myColor)?grp.myColor:css("--gps");
    c.beginPath();trail.forEach(function(q,k){var x=W/2+(q[2]-MV.u)*ws,y=H/2+(q[3]-MV.v)*ws;k?c.lineTo(x,y):c.moveTo(x,y)});
    c.strokeStyle=css("--surface");c.globalAlpha=.9;c.lineWidth=8.5;c.stroke();
    c.strokeStyle=tcol;c.globalAlpha=1;c.lineWidth=5;c.stroke();c.globalAlpha=1;
  }
  // ตำแหน่ง GPS จริง
  if(gpsFix){
    var gx=W/2+(gpsFix.u-MV.u)*ws,gy=H/2+(gpsFix.v-MV.v)*ws,mg=40075016.686*Math.cos(gpsFix.lat*Math.PI/180)/ws,ar=Math.max(9,gpsFix.acc/mg);
    if(offRoute&&gpsFix.ni!=null){
      var nx=X(gpsFix.ni),ny=Y(gpsFix.ni);
      c.beginPath();c.moveTo(gx,gy);c.lineTo(nx,ny);c.setLineDash([6,5]);c.lineWidth=2.5;c.strokeStyle=css("--bad");c.stroke();c.setLineDash([]);
      c.beginPath();c.arc(nx,ny,5,0,6.283);c.fillStyle=css("--bad");c.fill();
      c.font="600 12px "+css("--mono");c.textAlign="center";c.textBaseline="alphabetic";
      var lt=Math.round(gpsFix.off)+" ม.",lx=(gx+nx)/2,ly=(gy+ny)/2-6;
      c.lineWidth=3;c.strokeStyle=css("--surface");c.strokeText(lt,lx,ly);c.fillStyle=css("--bad");c.fillText(lt,lx,ly);
    }
    c.beginPath();c.arc(gx,gy,ar,0,6.283);c.fillStyle=css("--gps");c.globalAlpha=.16;c.fill();c.globalAlpha=1;
    ownMarker(c,gx,gy);
  }
  // รอยทางของเพื่อน
  grp.friends.forEach(function(f){var tr=grp.trails[f.id];if(!tr||tr.length<2)return;
    c.beginPath();tr.forEach(function(q,k){var x=W/2+(q[0]-MV.u)*ws,y=H/2+(q[1]-MV.v)*ws;k?c.lineTo(x,y):c.moveTo(x,y)});
    c.strokeStyle=css("--surface");c.globalAlpha=.85;c.lineWidth=7.5;c.stroke();c.strokeStyle=f.color;c.globalAlpha=f.stale?.5:1;c.lineWidth=4.5;c.stroke();c.globalAlpha=1});
  // เพื่อนในกลุ่ม
  grp.friends.forEach(function(f){var fx=W/2+(f.u-MV.u)*ws,fy=H/2+(f.v-MV.v)*ws;if(fx<-30||fx>W+30||fy<-30||fy>H+30)return;friendMarker(c,fx,fy,f)});
  // เครดิต
  c.font="10px "+css("--font");c.textAlign="right";c.textBaseline="alphabetic";
  var attr=attrText();
  if(attr){var tw=c.measureText(attr).width;c.fillStyle=css("--surface");c.globalAlpha=.8;c.fillRect(W-tw-12,H-17,tw+10,15);c.globalAlpha=1;c.fillStyle=css("--muted");c.fillText(attr,W-7,H-6)}
}
(function mapInput(){
  var cv=$("map"),ptrs=new Map(),prevD=0;
  function pos(e){var r=cv.getBoundingClientRect();return {x:e.clientX-r.left,y:e.clientY-r.top}}
  cv.addEventListener("pointerdown",function(e){try{cv.setPointerCapture(e.pointerId)}catch(x){}ptrs.set(e.pointerId,pos(e));prevD=0;cv.style.cursor="grabbing"});
  cv.addEventListener("pointermove",function(e){
    if(!ptrs.has(e.pointerId))return;var p=pos(e),o=ptrs.get(e.pointerId),ws=256*Math.pow(2,MV.z);
    if(ptrs.size===1){MV.u-=(p.x-o.x)/ws;MV.v=clamp(MV.v-(p.y-o.y)/ws,0,1);if(follow&&(Math.abs(p.x-o.x)+Math.abs(p.y-o.y)>2))setFollow(false)}
    ptrs.set(e.pointerId,p);
    if(ptrs.size===2){var a=Array.from(ptrs.values()),d=Math.hypot(a[0].x-a[1].x,a[0].y-a[1].y);
      if(prevD>0&&d>0)zoomAt((a[0].x+a[1].x)/2,(a[0].y+a[1].y)/2,Math.log(d/prevD)/Math.LN2);prevD=d}
    reqDraw();
  });
  function up(e){ptrs.delete(e.pointerId);prevD=0;cv.style.cursor="grab"}
  cv.addEventListener("pointerup",up);cv.addEventListener("pointercancel",up);
  cv.addEventListener("wheel",function(e){e.preventDefault();var p=pos(e);zoomAt(p.x,p.y,-e.deltaY*0.0018);reqDraw()},{passive:false});
  $("zIn").onclick=function(){zoomAt(MV.w/2,MV.h/2,1);reqDraw()};
  $("zOut").onclick=function(){zoomAt(MV.w/2,MV.h/2,-1);reqDraw()};
  $("zFit").onclick=function(){setFollow(false);fitRoute();reqDraw()};
  $("zFollow").onclick=function(){setFollow(!follow);reqDraw()};
})();

/* ================= satellite + 3D ================= */
var DEF_SAT="https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}";
var DEF_SAT_ATTR="Imagery © Esri, Maxar, Earthstar Geographics";
var DEF_DEM="https://s3.amazonaws.com/elevation-tiles-prod/terrarium/{z}/{x}/{y}.png";
var DEM_ATTR="ความสูง: Mapzen / AWS Terrain Tiles";
var mode3d=false,orbit=false,cam={b:0,p:55},EXS=[1,1.5,2,3,5];
var G={ok:null,gl:null,tex:new Map(),routeFor:null,lastRi:-2,lastSel:null,lastMuted:"",demOn:0,VP:null,u0:0,v0:0,mpu:1,base:0,eleMean:0,exI:0};

function baseUrl(z,x,y){
  var t=S.base==="sat"?(S.satUrl||DEF_SAT):(S.tileUrl||DEF_TILE);
  return t.replace("{z}",z).replace("{x}",x).replace("{y}",y);
}
function demUrl(z,x,y){return (S.demUrl||DEF_DEM).replace("{z}",z).replace("{x}",x).replace("{y}",y)}
function attrText(){
  if(S.base==="sat")return S.satUrl?(S.satAttr||""):DEF_SAT_ATTR;
  return S.tileUrl?(S.tileAttr||""):DEF_ATTR;
}
function setBase(b){
  S.base=b;save();$("mRoad").setAttribute("aria-pressed",b==="road");$("mSat").setAttribute("aria-pressed",b==="sat");reqDraw();
}
$("mRoad").onclick=function(){setBase("road")};
$("mSat").onclick=function(){setBase("sat")};

/* ---- matrices (column-major) ---- */
function m4persp(f,a,n,fr){var t=1/Math.tan(f/2),o=new Float32Array(16);o[0]=t/a;o[5]=t;o[10]=(fr+n)/(n-fr);o[11]=-1;o[14]=2*fr*n/(n-fr);return o}
function m4look(e,c,u){
  var f=[c[0]-e[0],c[1]-e[1],c[2]-e[2]],l=Math.hypot(f[0],f[1],f[2]);f=[f[0]/l,f[1]/l,f[2]/l];
  var s=[f[1]*u[2]-f[2]*u[1],f[2]*u[0]-f[0]*u[2],f[0]*u[1]-f[1]*u[0]];l=Math.hypot(s[0],s[1],s[2]);s=[s[0]/l,s[1]/l,s[2]/l];
  var v=[s[1]*f[2]-s[2]*f[1],s[2]*f[0]-s[0]*f[2],s[0]*f[1]-s[1]*f[0]],m=new Float32Array(16);
  m[0]=s[0];m[4]=s[1];m[8]=s[2];m[12]=-(s[0]*e[0]+s[1]*e[1]+s[2]*e[2]);
  m[1]=v[0];m[5]=v[1];m[9]=v[2];m[13]=-(v[0]*e[0]+v[1]*e[1]+v[2]*e[2]);
  m[2]=-f[0];m[6]=-f[1];m[10]=-f[2];m[14]=f[0]*e[0]+f[1]*e[1]+f[2]*e[2];m[15]=1;return m;
}
function m4mul(a,b){var o=new Float32Array(16);for(var i=0;i<4;i++)for(var j=0;j<4;j++){var s=0;for(var k=0;k<4;k++)s+=a[k*4+i]*b[j*4+k];o[j*4+i]=s}return o}
function hexRGB(h){h=(h||"").trim();if(h[0]!=="#")return [.5,.5,.5];if(h.length===4)h="#"+h[1]+h[1]+h[2]+h[2]+h[3]+h[3];
  return [parseInt(h.substr(1,2),16)/255,parseInt(h.substr(3,2),16)/255,parseInt(h.substr(5,2),16)/255]}

/* ---- shaders ---- */
var VS_T=[
"precision highp float;",
"attribute vec2 aG;",
"uniform mat4 uVP;uniform vec3 uTile;uniform vec4 uDemT;uniform float uGrid,uEx,uBase,uSkirt;",
"uniform highp sampler2D uDem;",
"varying vec2 vUV;varying float vSh;",
"float dec(highp vec4 c){return c.r*65280.0+c.g*255.0+c.b*0.99609375-32768.0;}",
"highp vec4 tap(vec2 p){vec2 e=vec2(0.5/256.0);return texture2D(uDem,clamp(p,e,1.0-e));}",
"float hAt(vec2 g){vec2 t=uDemT.xy+g*uDemT.z;vec2 p=t*256.0-0.5;vec2 i=floor(p);vec2 f=p-i;vec2 b=(i+0.5)/256.0;",
" float h00=dec(tap(b)),h10=dec(tap(b+vec2(1.0/256.0,0.0))),h01=dec(tap(b+vec2(0.0,1.0/256.0))),h11=dec(tap(b+vec2(1.0/256.0)));",
" return mix(mix(h00,h10,f.x),mix(h01,h11,f.x),f.y);}",
"void main(){",
" vec2 g=clamp((aG-1.0)/uGrid,0.0,1.0);",
" float sk=(aG.x<0.5||aG.y<0.5||aG.x>uGrid+1.5||aG.y>uGrid+1.5)?1.0:0.0;",
" float h=0.0;float sh=1.0;",
" if(uDemT.w>0.5){",
"  h=hAt(g);float d=2.0/uGrid;",
"  vec2 gx1=min(g+vec2(d,0.0),1.0),gx0=max(g-vec2(d,0.0),0.0),gy1=min(g+vec2(0.0,d),1.0),gy0=max(g-vec2(0.0,d),0.0);",
"  float dzx=(hAt(gx1)-hAt(gx0))*uEx/((gx1.x-gx0.x)*uTile.z);",
"  float dzy=-(hAt(gy1)-hAt(gy0))*uEx/((gy1.y-gy0.y)*uTile.z);",
"  vec3 n=normalize(vec3(-dzx,-dzy,1.0));",
"  sh=0.5+0.65*clamp(dot(n,normalize(vec3(-0.55,0.6,0.75))),0.0,1.0);",
" }",
" float z=uDemT.w>0.5?(h-uBase)*uEx:0.0;",
" z-=sk*uSkirt;",
" vec2 w=vec2(uTile.x+g.x*uTile.z,uTile.y-g.y*uTile.z);",
" vUV=g;vSh=sh;gl_Position=uVP*vec4(w,z,1.0);}"
].join("\n");
var FS_T=[
"precision mediump float;varying vec2 vUV;varying float vSh;uniform sampler2D uImg;uniform float uHasImg;uniform vec3 uBg;",
"void main(){vec3 c=uHasImg>0.5?texture2D(uImg,vUV).rgb:uBg;gl_FragColor=vec4(c*vSh,1.0);}"
].join("\n");
var VS_R=[
"precision highp float;attribute vec3 aP,aQ;attribute vec2 aS;attribute vec3 aC;",
"uniform mat4 uVP;uniform vec2 uRes;uniform float uW,uEx,uBase,uDemOn,uLift,uCase;uniform vec3 uCaseC;",
"varying vec3 vC;",
"vec4 pr(vec3 p){return uVP*vec4(p.xy,(p.z-uBase)*uEx*uDemOn+uLift,1.0);}",
"void main(){vec4 p=pr(aP),q=pr(aQ);vec2 sp=p.xy/p.w*uRes*0.5,sq=q.xy/q.w*uRes*0.5;",
" vec2 dv=aS.y<0.5?sq-sp:sp-sq;float l=length(dv);vec2 dir=l>0.0001?dv/l:vec2(1.0,0.0);",
" sp+=(aS.y<0.5?-dir:dir)*uW*0.5;sp+=vec2(-dir.y,dir.x)*aS.x*uW*0.5;",
" gl_Position=vec4(sp/(uRes*0.5)*p.w,p.z,p.w);vC=uCase>0.5?uCaseC:aC;}"
].join("\n");
var FS_R="precision mediump float;varying vec3 vC;void main(){gl_FragColor=vec4(vC,1.0);}";

function compile(gl,type,src){var s=gl.createShader(type);gl.shaderSource(s,src);gl.compileShader(s);
  if(!gl.getShaderParameter(s,gl.COMPILE_STATUS))throw new Error(gl.getShaderInfoLog(s));return s}
function program(gl,vs,fs){var p=gl.createProgram();gl.attachShader(p,compile(gl,gl.VERTEX_SHADER,vs));gl.attachShader(p,compile(gl,gl.FRAGMENT_SHADER,fs));
  gl.linkProgram(p);if(!gl.getProgramParameter(p,gl.LINK_STATUS))throw new Error(gl.getProgramInfoLog(p));
  var u={},n=gl.getProgramParameter(p,gl.ACTIVE_UNIFORMS),i;for(i=0;i<n;i++){var nm=gl.getActiveUniform(p,i).name;u[nm]=gl.getUniformLocation(p,nm)}
  return {p:p,u:u}}

function glInit(){
  if(G.ok!==null)return G.ok;
  try{
    var cv=$("glc"),gl=cv.getContext("webgl2",{antialias:true,alpha:false})||cv.getContext("webgl",{antialias:true,alpha:false});
    if(!gl)throw new Error("no webgl");
    if(gl.getParameter(gl.MAX_VERTEX_TEXTURE_IMAGE_UNITS)<1)throw new Error("no vtf");
    if(!(window.WebGL2RenderingContext&&gl instanceof WebGL2RenderingContext)&&!gl.getExtension("OES_element_index_uint"))throw new Error("no uint index");
    G.gl=gl;G.T=program(gl,VS_T,FS_T);G.R=program(gl,VS_R,FS_R);
    // ตาข่ายของไทล์: (N+3)^2 จุด รวมขอบกันรอยแยก (skirt)
    var N=64,M=N+3,vs=new Float32Array(M*M*2),ix=[],i,j;
    for(j=0;j<M;j++)for(i=0;i<M;i++){vs[(j*M+i)*2]=i;vs[(j*M+i)*2+1]=j}
    for(j=0;j<M-1;j++)for(i=0;i<M-1;i++){var a=j*M+i,b=a+1,c=a+M,d=c+1;ix.push(a,c,b,b,c,d)}
    G.grid=N;G.nIdx=ix.length;
    G.bufG=gl.createBuffer();gl.bindBuffer(gl.ARRAY_BUFFER,G.bufG);gl.bufferData(gl.ARRAY_BUFFER,vs,gl.STATIC_DRAW);
    G.bufI=gl.createBuffer();gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER,G.bufI);gl.bufferData(gl.ELEMENT_ARRAY_BUFFER,new Uint16Array(ix),gl.STATIC_DRAW);
    G.blank=gl.createTexture();gl.bindTexture(gl.TEXTURE_2D,G.blank);gl.texImage2D(gl.TEXTURE_2D,0,gl.RGBA,1,1,0,gl.RGBA,gl.UNSIGNED_BYTE,new Uint8Array([128,128,128,255]));
    G.ok=true;
  }catch(e){G.ok=false;G.err=e&&e.message}
  return G.ok;
}

function texFor(img,isDem){
  var gl=G.gl;
  if(!img||!img.complete||!img.naturalWidth||img._noCors||img._bad)return null;
  var t=G.tex.get(img.src);if(t)return t;
  try{
    t=gl.createTexture();gl.bindTexture(gl.TEXTURE_2D,t);
    gl.pixelStorei(gl.UNPACK_COLORSPACE_CONVERSION_WEBGL,isDem?gl.NONE:gl.BROWSER_DEFAULT_WEBGL);
    gl.pixelStorei(gl.UNPACK_PREMULTIPLY_ALPHA_WEBGL,false);
    gl.texImage2D(gl.TEXTURE_2D,0,gl.RGBA,gl.RGBA,gl.UNSIGNED_BYTE,img);
    var f=isDem?gl.NEAREST:gl.LINEAR,wi=img.naturalWidth,hi=img.naturalHeight,pot=(wi&(wi-1))===0&&(hi&(hi-1))===0,isG2=!!(window.WebGL2RenderingContext&&gl instanceof WebGL2RenderingContext);
    if(!isDem&&(pot||isG2)){gl.generateMipmap(gl.TEXTURE_2D);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MIN_FILTER,gl.LINEAR_MIPMAP_LINEAR);
      var an=gl.getExtension("EXT_texture_filter_anisotropic");if(an)gl.texParameterf(gl.TEXTURE_2D,an.TEXTURE_MAX_ANISOTROPY_EXT,Math.min(8,gl.getParameter(an.MAX_TEXTURE_MAX_ANISOTROPY_EXT)))}
    else gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MIN_FILTER,f);
    gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MAG_FILTER,f);
    gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_S,gl.CLAMP_TO_EDGE);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_T,gl.CLAMP_TO_EDGE);
  }catch(e){img._bad=true;return null}
  if(G.tex.size>300){var n=0;G.tex.forEach(function(v,k){if(n++<80){gl.deleteTexture(v);G.tex.delete(k)}})}
  G.tex.set(img.src,t);return t;
}

/* ---- เส้นทางสำหรับ 3D ---- */
function buildRoute3d(){
  var gl=G.gl,n=route.n,i,u0=0,v0=0,mn=1e9,sum=0;
  for(i=0;i<=n;i++){u0+=route.mu[i];v0+=route.mv[i];if(route.se[i]<mn)mn=route.se[i];sum+=route.se[i]}
  G.u0=u0/(n+1);G.v0=v0/(n+1);G.mpu=40075016.686*Math.cos(route.lat[Math.floor(n/2)]*Math.PI/180);G.base=mn;G.eleMean=sum/(n+1);
  var X=function(k){return (route.mu[k]-G.u0)*G.mpu},Y=function(k){return -(route.mv[k]-G.v0)*G.mpu};
  var geo=new Float32Array(n*4*8),idx=new Uint32Array(n*6),o=0;
  for(i=0;i<n;i++){
    var P=i,Q=i+1,defs=[[P,Q,-1,0],[P,Q,1,0],[Q,P,-1,1],[Q,P,1,1]];
    for(var d=0;d<4;d++){var a=defs[d][0],b=defs[d][1];
      geo[o++]=X(a);geo[o++]=Y(a);geo[o++]=route.se[a];geo[o++]=X(b);geo[o++]=Y(b);geo[o++]=route.se[b];geo[o++]=defs[d][2];geo[o++]=defs[d][3]}
    var v=i*4;idx.set([v,v+1,v+2,v+2,v+1,v+3],i*6);
  }
  G.nSeg=n;G.bufGeo=G.bufGeo||gl.createBuffer();gl.bindBuffer(gl.ARRAY_BUFFER,G.bufGeo);gl.bufferData(gl.ARRAY_BUFFER,geo,gl.STATIC_DRAW);
  G.bufRI=G.bufRI||gl.createBuffer();gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER,G.bufRI);gl.bufferData(gl.ELEMENT_ARRAY_BUFFER,idx,gl.STATIC_DRAW);
  G.bufCol=G.bufCol||gl.createBuffer();G.col=new Float32Array(n*4*3);
  G.gcol=new Float32Array(n*3);for(i=0;i<n;i++){var c=gcRGB(route.grade[i]);G.gcol[i*3]=c[0]/255;G.gcol[i*3+1]=c[1]/255;G.gcol[i*3+2]=c[2]/255}
  G.routeFor=route;G.lastRi=-2;G.lastSel=null;
}
function updateColors3d(ri){
  var gl=G.gl,n=G.nSeg,muted=css("--muted"),mc=hexRGB(muted),ink=hexRGB(css("--ink")),i,k;
  for(i=0;i<n;i++){
    var c;
    if(selSeg&&i>=selSeg.a&&i<selSeg.b)c=ink;
    else if(i<ri)c=mc;
    else c=[G.gcol[i*3],G.gcol[i*3+1],G.gcol[i*3+2]];
    for(k=0;k<4;k++){var q=(i*4+k)*3;G.col[q]=c[0];G.col[q+1]=c[1];G.col[q+2]=c[2]}
  }
  gl.bindBuffer(gl.ARRAY_BUFFER,G.bufCol);gl.bufferData(gl.ARRAY_BUFFER,G.col,gl.DYNAMIC_DRAW);
  G.lastRi=ri;G.lastSel=selSeg;G.lastMuted=muted;
}

/* ---- วาด 3D ---- */
function draw3d(){
  var ov=$("map3d");if(ov.offsetParent===null||!route)return;
  if(G.routeFor!==route)buildRoute3d();
  var gl=G.gl,r=ov.getBoundingClientRect(),W=r.width,H=r.height,dpr=Math.min(window.devicePixelRatio||1,2);
  var gw=Math.round(W*dpr),gh=Math.round(H*dpr),glc=$("glc");
  if(glc.width!==gw||glc.height!==gh){glc.width=gw;glc.height=gh}
  if(ov.width!==gw||ov.height!==gh){ov.width=gw;ov.height=gh}
  MV.w=W;MV.h=H;
  var ex=EXS[G.exI],ri=idxAt(runnerKm());
  if(G.lastRi!==ri||G.lastSel!==selSeg||G.lastMuted!==css("--muted"))updateColors3d(ri);
  // กล้อง
  var fov=0.7854,mpp=G.mpu/(256*Math.pow(2,MV.z)),d=(H*mpp/2)/Math.tan(fov/2);
  var pr=clamp(cam.p,2,75)*Math.PI/180,bb=cam.b*Math.PI/180,hx=Math.sin(bb),hy=Math.cos(bb);
  var tx=(MV.u-G.u0)*G.mpu,ty=-(MV.v-G.v0)*G.mpu,tz=G.demOn?(G.eleMean-G.base)*ex:0;
  var eye=[tx-d*Math.sin(pr)*hx,ty-d*Math.sin(pr)*hy,tz+d*Math.cos(pr)];
  var VP=m4mul(m4persp(fov,W/H,d*0.02,d*60),m4look(eye,[tx,ty,tz],[0,0,1]));G.VP=VP;
  // พื้นหลัง
  var bg=hexRGB(css("--bg"));
  gl.viewport(0,0,gw,gh);gl.clearColor(bg[0],bg[1],bg[2],1);gl.clear(gl.COLOR_BUFFER_BIT|gl.DEPTH_BUFFER_BIT);
  // ภูมิประเทศ
  var T=G.T,z0=clamp(Math.round(MV.z),3,16),nt=Math.pow(2,z0),cx=Math.floor(MV.u*nt),cy=Math.floor(MV.v*nt),R=z0>=13?3:2;
  var surf=hexRGB(css("--surface")),dz=Math.min(z0,14),sh=z0-dz,sc=1/Math.pow(2,sh),centerDem=0,loading=0,imgFail=0;
  gl.useProgram(T.p);gl.enable(gl.DEPTH_TEST);gl.depthFunc(gl.LEQUAL);gl.disable(gl.BLEND);
  gl.bindBuffer(gl.ARRAY_BUFFER,G.bufG);var aG=gl.getAttribLocation(T.p,"aG");gl.enableVertexAttribArray(aG);gl.vertexAttribPointer(aG,2,gl.FLOAT,false,0,0);
  gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER,G.bufI);
  gl.uniformMatrix4fv(T.u.uVP,false,VP);gl.uniform1f(T.u.uGrid,G.grid);gl.uniform1f(T.u.uEx,ex);gl.uniform1f(T.u.uBase,G.base);gl.uniform1f(T.u.uSkirt,500);
  gl.uniform3f(T.u.uBg,surf[0],surf[1],surf[2]);gl.uniform1i(T.u.uImg,0);gl.uniform1i(T.u.uDem,1);
  for(var ty2=cy-R;ty2<=cy+R;ty2++){
    if(ty2<0||ty2>=nt)continue;
    for(var tx2=cx-R;tx2<=cx+R;tx2++){
      var wx=((tx2%nt)+nt)%nt,img=getImg(baseUrl(z0,wx,ty2)),tex=texFor(img,false);
      if(!tex){if(img&&img._noCors&&img.complete&&img.naturalWidth)imgFail++;else if(img&&img._bad)imgFail++;else if(!(img&&img._dead))loading++}
      var dx=wx>>sh,dy=ty2>>sh,dimg=getImg(demUrl(dz,dx,dy)),dtex=texFor(dimg,true);
      gl.activeTexture(gl.TEXTURE0);gl.bindTexture(gl.TEXTURE_2D,tex||G.blank);gl.uniform1f(T.u.uHasImg,tex?1:0);
      gl.activeTexture(gl.TEXTURE1);gl.bindTexture(gl.TEXTURE_2D,dtex||G.blank);
      gl.uniform4f(T.u.uDemT,(wx/Math.pow(2,sh))-dx,(ty2/Math.pow(2,sh))-dy,sc,dtex?1:0);
      gl.uniform3f(T.u.uTile,(tx2/nt-G.u0)*G.mpu,-(ty2/nt-G.v0)*G.mpu,G.mpu/nt);
      gl.drawElements(gl.TRIANGLES,G.nIdx,gl.UNSIGNED_SHORT,0);
      if(dtex&&tx2===cx&&ty2===cy)centerDem=1;
    }
  }
  gl.disableVertexAttribArray(aG);
  var wasOn=G.demOn;G.demOn=centerDem;if(wasOn!==centerDem){reqDraw()}
  // เส้นทาง (ไม่ตรวจความลึก วาดทับเสมอ)
  var Rp=G.R;gl.useProgram(Rp.p);gl.disable(gl.DEPTH_TEST);
  gl.uniformMatrix4fv(Rp.u.uVP,false,VP);gl.uniform2f(Rp.u.uRes,gw,gh);gl.uniform1f(Rp.u.uEx,ex);gl.uniform1f(Rp.u.uBase,G.base);gl.uniform1f(Rp.u.uDemOn,G.demOn);gl.uniform1f(Rp.u.uLift,6);
  gl.bindBuffer(gl.ARRAY_BUFFER,G.bufGeo);
  var aP=gl.getAttribLocation(Rp.p,"aP"),aQ=gl.getAttribLocation(Rp.p,"aQ"),aS=gl.getAttribLocation(Rp.p,"aS"),aC=gl.getAttribLocation(Rp.p,"aC");
  gl.enableVertexAttribArray(aP);gl.vertexAttribPointer(aP,3,gl.FLOAT,false,32,0);
  gl.enableVertexAttribArray(aQ);gl.vertexAttribPointer(aQ,3,gl.FLOAT,false,32,12);
  gl.enableVertexAttribArray(aS);gl.vertexAttribPointer(aS,2,gl.FLOAT,false,32,24);
  gl.bindBuffer(gl.ARRAY_BUFFER,G.bufCol);gl.enableVertexAttribArray(aC);gl.vertexAttribPointer(aC,3,gl.FLOAT,false,0,0);
  gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER,G.bufRI);
  var cc=hexRGB(css("--surface"));
  gl.uniform1f(Rp.u.uCase,1);gl.uniform3f(Rp.u.uCaseC,cc[0],cc[1],cc[2]);gl.uniform1f(Rp.u.uW,14*dpr);gl.drawElements(gl.TRIANGLES,G.nSeg*6,gl.UNSIGNED_INT,0);
  gl.uniform1f(Rp.u.uCase,0);gl.uniform1f(Rp.u.uW,9*dpr);gl.drawElements(gl.TRIANGLES,G.nSeg*6,gl.UNSIGNED_INT,0);
  gl.disableVertexAttribArray(aP);gl.disableVertexAttribArray(aQ);gl.disableVertexAttribArray(aS);gl.disableVertexAttribArray(aC);

  // ส่วนซ้อนทับ: หมุด ป้าย ตำแหน่ง GPS
  var c=ov.getContext("2d");c.setTransform(dpr,0,0,dpr,0,0);c.clearRect(0,0,W,H);
  var demOn=G.demOn,zOf=function(k){return (route.se[k]-G.base)*ex*demOn+6};
  var proj=function(x,y,z){var m=VP,px=m[0]*x+m[4]*y+m[8]*z+m[12],py=m[1]*x+m[5]*y+m[9]*z+m[13],pw=m[3]*x+m[7]*y+m[11]*z+m[15];
    if(pw<=0)return null;return [(px/pw*0.5+0.5)*W,(1-(py/pw*0.5+0.5))*H]};
  var rp=function(k){return proj((route.mu[k]-G.u0)*G.mpu,-(route.mv[k]-G.v0)*G.mpu,zOf(k))};
  c.font="600 12px "+css("--mono");c.textBaseline="middle";c.lineJoin="round";
  cps.forEach(function(cp){var p=rp(idxAt(Math.min(cp.km,route.total/1000)));if(!p)return;
    c.beginPath();c.arc(p[0],p[1],6,0,6.283);c.fillStyle=css("--surface");c.fill();c.lineWidth=2.5;c.strokeStyle=css("--ink");c.stroke();
    var right=p[0]>W-80;c.textAlign=right?"right":"left";var tx3=p[0]+(right?-11:11);
    c.lineWidth=3;c.strokeStyle=css("--surface");c.strokeText(cp.name,tx3,p[1]-11);c.fillStyle=css("--ink");c.fillText(cp.name,tx3,p[1]-11)});
  var strokeLine3=function(pts,col,alpha){ // pts: [u,v,ni]
    var step=Math.max(1,Math.ceil(pts.length/1500));
    var pp=[],k;for(k=0;k<pts.length;k+=step){var q=pts[k],ni=q[2];if(ni==null){ni=nearestIn(merc2lat(q[1]),q[0]*360-180,0,route.n).i;q[2]=ni}
      pp.push(proj((q[0]-G.u0)*G.mpu,-(q[1]-G.v0)*G.mpu,zOf(clamp(ni,0,route.n))))}
    if(pp.length<2)return;
    var path=function(){var open=false;c.beginPath();pp.forEach(function(p){if(!p){open=false;return}open?c.lineTo(p[0],p[1]):c.moveTo(p[0],p[1]);open=true})};
    c.lineJoin="round";c.lineCap="round";path();c.strokeStyle=css("--surface");c.globalAlpha=.9*alpha;c.lineWidth=9;c.stroke();
    path();c.strokeStyle=col;c.globalAlpha=alpha;c.lineWidth=5.5;c.stroke();c.globalAlpha=1};
  grp.friends.forEach(function(f){var tr=grp.trails[f.id];if(tr&&tr.length>1)strokeLine3(tr,f.color,f.stale?.5:1)});
  if(trail.length>1){var tr3=trail.map(function(q){return [q[2],q[3],q[4]]});strokeLine3(tr3,(grp.on&&!S.gView&&grp.myColor)?grp.myColor:css("--gps"),1)}
  var s0=rp(0);if(s0){c.beginPath();c.arc(s0[0],s0[1],5,0,6.283);c.fillStyle=css("--ok");c.fill();c.lineWidth=2;c.strokeStyle=css("--surface");c.stroke()}
  var rr=rp(ri);
  if(gpsFix){
    var gz=zOf(clamp(gpsFix.ni!=null?gpsFix.ni:ri,0,route.n)),gp=proj((gpsFix.u-G.u0)*G.mpu,-(gpsFix.v-G.v0)*G.mpu,gz);
    if(gp){
      if(offRoute&&gpsFix.ni!=null){var np=rp(gpsFix.ni);
        if(np){c.beginPath();c.moveTo(gp[0],gp[1]);c.lineTo(np[0],np[1]);c.setLineDash([6,5]);c.lineWidth=2.5;c.strokeStyle=css("--bad");c.stroke();c.setLineDash([]);
          c.beginPath();c.arc(np[0],np[1],5,0,6.283);c.fillStyle=css("--bad");c.fill();
          var lt=Math.round(gpsFix.off)+" ม.";c.textAlign="center";c.textBaseline="alphabetic";c.lineWidth=3;c.strokeStyle=css("--surface");
          c.strokeText(lt,(gp[0]+np[0])/2,(gp[1]+np[1])/2-6);c.fillStyle=css("--bad");c.fillText(lt,(gp[0]+np[0])/2,(gp[1]+np[1])/2-6)}}
      c.beginPath();c.arc(gp[0],gp[1],Math.max(9,gpsFix.acc/mpp),0,6.283);c.fillStyle=css("--gps");c.globalAlpha=.16;c.fill();c.globalAlpha=1;
      ownMarker(c,gp[0],gp[1]);
    }
  }
  if(rr){c.beginPath();c.arc(rr[0],rr[1],13,0,6.283);c.fillStyle=css("--accent");c.globalAlpha=.25;c.fill();c.globalAlpha=1;
    if(gpsFix){c.beginPath();c.arc(rr[0],rr[1],7,0,6.283);c.fillStyle=css("--accent");c.fill();c.lineWidth=2.5;c.strokeStyle=css("--surface");c.stroke()}else ownMarker(c,rr[0],rr[1])}
  grp.friends.forEach(function(f){
    var fp=proj((f.u-G.u0)*G.mpu,-(f.v-G.v0)*G.mpu,zOf(clamp(f.ni||0,0,route.n)));if(fp)friendMarker(c,fp[0],fp[1],f)});
  // สถานะมุมกล้อง + เครดิต
  c.font="10px "+css("--font");c.textBaseline="alphabetic";
  var info="3D · เอียง "+Math.round(cam.p)+"° · สูง ×"+ex,at=[attrText(),G.demOn?DEM_ATTR:""].filter(Boolean).join(" · ");
  var tw=c.measureText(info).width;c.fillStyle=css("--surface");c.globalAlpha=.8;c.fillRect(8,H-19,tw+10,15);c.globalAlpha=1;c.fillStyle=css("--muted");c.textAlign="left";c.fillText(info,13,H-8);
  if(at){c.textAlign="right";tw=c.measureText(at).width;c.fillStyle=css("--surface");c.globalAlpha=.8;c.fillRect(W-tw-12,2,tw+10,15);c.globalAlpha=1;c.fillStyle=css("--muted");c.fillText(at,W-7,13)}
  // ข้อความสถานะ
  var nt2=$("mapNote");
  nt2.textContent=imgFail?"ภาพแผนที่ชุดนี้ไม่อนุญาตให้ใช้ใน 3D (CORS) ลองเปลี่ยนแหล่งภาพในแท็บตั้งค่า":
    (!G.demOn?(loading?"กำลังโหลดภูมิประเทศ... (ต้องออนไลน์ครั้งแรก)":"ยังไม่มีข้อมูลความสูงภูมิประเทศ แสดงเป็นพื้นราบ ตรวจอินเทอร์เน็ตหรือลิงก์ข้อมูลความสูง"):"");
  $("r3N").style.transform="rotate("+(-cam.b)+"deg)";
  if(loading)setTimeout(reqDraw,700); // ไทล์ที่ยังโหลดไม่เสร็จ: วาดซ้ำเมื่อพร้อม
}

function set3d(on){
  if(on&&!glInit()){$("mapNote").textContent="อุปกรณ์หรือเบราว์เซอร์นี้เปิด 3D ไม่ได้ ("+(G.err||"WebGL")+")";return}
  mode3d=on;$("m3d").setAttribute("aria-pressed",on);
  $("map").hidden=on;$("glc").hidden=!on;$("map3d").hidden=!on;$("ctl3d").hidden=!on;
  $("mapNote").textContent="";reqDraw();
}
$("m3d").onclick=function(){set3d(!mode3d)};
$("r3L").onclick=function(){cam.b=(cam.b-30)%360;reqDraw()};
$("r3R").onclick=function(){cam.b=(cam.b+30)%360;reqDraw()};
$("r3N").onclick=function(){cam.b=0;reqDraw()};
$("r3U").onclick=function(){cam.p=clamp(cam.p-10,0,75);reqDraw()};
$("r3D").onclick=function(){cam.p=clamp(cam.p+10,0,75);reqDraw()};
$("r3M").onclick=function(){orbit=!orbit;$("r3M").textContent=orbit?"ลาก:หมุน":"ลาก:เลื่อน";$("r3M").setAttribute("aria-pressed",orbit)};
$("r3E").onclick=function(){G.exI=(G.exI+1)%EXS.length;$("r3E").textContent="สูง×"+EXS[G.exI];S.ex=EXS[G.exI];save();reqDraw()};
(function input3d(){
  var cv=$("map3d"),ptrs=new Map(),prevD=0,prevA=0;
  function pos(e){var r=cv.getBoundingClientRect();return {x:e.clientX-r.left,y:e.clientY-r.top}}
  function pan(dx,dy){
    var mpp=G.mpu/(256*Math.pow(2,MV.z)),b=cam.b*Math.PI/180,k=1/Math.max(Math.cos(clamp(cam.p,0,75)*Math.PI/180),.35);
    var east=-dx*Math.cos(b)*mpp+dy*k*Math.sin(b)*mpp,north=dx*Math.sin(b)*mpp+dy*k*Math.cos(b)*mpp;
    MV.u+=east/G.mpu;MV.v=clamp(MV.v-north/G.mpu,0,1);
  }
  cv.addEventListener("contextmenu",function(e){e.preventDefault()});
  cv.addEventListener("pointerdown",function(e){try{cv.setPointerCapture(e.pointerId)}catch(x){}ptrs.set(e.pointerId,pos(e));prevD=0;prevA=0});
  cv.addEventListener("pointermove",function(e){
    if(!ptrs.has(e.pointerId))return;var p=pos(e),o=ptrs.get(e.pointerId);
    if(ptrs.size===1){
      if(orbit||e.shiftKey||e.buttons===2){cam.b=(cam.b-(p.x-o.x)*0.4)%360;cam.p=clamp(cam.p+(p.y-o.y)*0.3,0,75)}
      else{pan(p.x-o.x,p.y-o.y);if(follow&&Math.abs(p.x-o.x)+Math.abs(p.y-o.y)>2)setFollow(false)}
    }
    ptrs.set(e.pointerId,p);
    if(ptrs.size===2){var a=Array.from(ptrs.values()),d=Math.hypot(a[0].x-a[1].x,a[0].y-a[1].y),an=Math.atan2(a[1].y-a[0].y,a[1].x-a[0].x)*180/Math.PI;
      if(prevD>0&&d>0){MV.z=clamp(MV.z+Math.log(d/prevD)/Math.LN2,3,18);var da=an-prevA;if(da>180)da-=360;if(da<-180)da+=360;cam.b=(cam.b-da)%360}
      prevD=d;prevA=an}
    reqDraw();
  });
  function up(e){ptrs.delete(e.pointerId);prevD=0}
  cv.addEventListener("pointerup",up);cv.addEventListener("pointercancel",up);
  cv.addEventListener("wheel",function(e){e.preventDefault();MV.z=clamp(MV.z-e.deltaY*0.0018,3,18);reqDraw()},{passive:false});
})();

/* ================= เต็มจอ ================= */
var full=false;
function updHud(){
  if(!full)return;
  $("mapHud").textContent=$("cLabel").textContent.split(" · ")[0]+" · "+$("count").textContent+" · "+$("sKm").textContent+" · ชัน "+$("sGrade").textContent;
}
function setFull(on){
  full=on;$("mapbox").classList.toggle("full",on);document.body.style.overflow=on?"hidden":"";
  $("zFull").textContent=on?"✕":"⛶";$("zFull").setAttribute("aria-label",on?"ออกจากเต็มจอ":"เต็มจอ");$("mapHud").hidden=!on;
  if(on){try{var el=document.documentElement;if(el.requestFullscreen)el.requestFullscreen({navigationUI:"hide"}).catch(function(){})}catch(e){}}
  else if(document.fullscreenElement){try{document.exitFullscreen()}catch(e){}}
  updHud();reqDraw();setTimeout(reqDraw,120);
}
$("zFull").onclick=function(){setFull(!full)};
document.addEventListener("fullscreenchange",function(){if(!document.fullscreenElement&&full)setFull(false);else reqDraw()});
document.addEventListener("keydown",function(e){if(e.key==="Escape"&&full)setFull(false)});
setInterval(updHud,1000);

/* ================= hill list ================= */
function renderLegend(){
  var parts=[],g;for(g=-20;g<=22;g+=2)parts.push(gc(g)+" "+((g+20)/42*100).toFixed(1)+"%");
  $("legend").innerHTML='<span>ลง</span><span class="bar" style="background:linear-gradient(90deg,'+parts.join(",")+')"></span><span>ขึ้นชัน</span>';
}
function renderHills(){
  var box=$("hills");box.innerHTML="";
  if(!route){box.innerHTML='<div class="hempty">ยังไม่มีเส้นทาง</div>';return}
  var list=route.segs.filter(function(s){return hillFilter==="all"?(s.gain>=S.minGain||s.loss>=S.minGain):(s.up&&s.gain>=S.minGain)});
  var head=document.createElement("div");head.className="hhead";
  head.innerHTML="<span>ช่วง</span><span>ชัน</span><span>ขึ้น</span><span>ลง</span>";box.appendChild(head);
  if(!list.length){var em=document.createElement("div");em.className="hempty";em.textContent="ไม่มีช่วงที่เข้าเงื่อนไข ลองลดค่า 'ทางขึ้นสูงอย่างน้อย' ในแท็บตั้งค่า";box.appendChild(em);return}
  var km=runnerKm();
  list.forEach(function(s){
    var b=document.createElement("button");b.className="hrow";b.type="button";
    var a=s.a*route.step/1000,e=s.b*route.step/1000;
    var title=s.up?("ทางขึ้น "+(s.cn?s.cn+"/"+(climbs.length):"-")):"ทางลง";
    if(km>=a&&km<=e)b.classList.add("now");
    if(selSeg===s)b.classList.add("sel");
    b.innerHTML='<span class="name"><i class="chip" style="background:'+gc(s.avg)+'"></i><span><span class="t">'+title+'</span><span class="s">กม. '+a.toFixed(1)+"–"+e.toFixed(1)+" · ยาว "+(s.len/1000).toFixed(2)+" กม. · "+(s.up?"ชันสุด ":"ลงชันสุด ")+Math.abs(s.maxG).toFixed(0)+'%</span></span></span>'+
      '<span class="n mono">'+sgn(s.avg,0)+'%</span><span class="n mono">'+Math.round(s.gain)+' ม.</span><span class="n mono">'+Math.round(s.loss)+' ม.</span>';
    b.onclick=function(){selSeg=(selSeg===s)?null:s;renderHills();drawCharts();reqDraw();
      if(selSeg){$("scrub").textContent=title+" · กม. "+a.toFixed(1)+"–"+e.toFixed(1)+" · เฉลี่ย "+sgn(s.avg,0)+"%"}}
    box.appendChild(b);
  });
}
function filterBtns(){$("fUp").setAttribute("aria-pressed",hillFilter==="up");$("fAll").setAttribute("aria-pressed",hillFilter==="all")}
$("fUp").onclick=function(){hillFilter="up";filterBtns();renderHills()};
$("fAll").onclick=function(){hillFilter="all";filterBtns();renderHills()};
/* ===== กราฟทางชัน: ซูม เลื่อน (แถบเลื่อน) เต็มจอ ===== */
(function(){
  var ov=$("pfull"),L=42,R=10,c2=$("prof2"),c3=$("prof3");
  function span(){return pv.b-pv.a}
  function sbUpd(){["sb2","sb3"].forEach(function(id){var sb=$(id),t=sb.firstChild;t.style.left=(pv.a*100)+"%";t.style.width=(span()*100)+"%";sb.classList.toggle("off",span()>=0.999)})}
  function redraw(){if(!$("p-hill").hidden)drawProfile(c2,true);if(!ov.hidden)drawProfile(c3,true);sbUpd()}
  function setView(a,b){var w=clamp(b-a,0.01,1);a=clamp(a,0,1-w);pv.a=a;pv.b=a+w;redraw()}
  function zoomAt(f,k){var w=clamp(span()*k,0.01,1),rel=(f-pv.a)/span();setView(f-rel*w,f-rel*w+w)}
  function scrubTxt(){if(!route||scrubKm==null)return;var i=idxAt(scrubKm),t="กม. "+scrubKm.toFixed(2)+" · สูง "+Math.round(route.se[i])+" ม. · ชัน "+sgn(route.grade[i],1)+"%";$("scrub").textContent=t;$("pfInfo").textContent=t}
  function attach(cv,full){
    var ptr={},pinch=null,drag=null;
    function rect(){return cv.getBoundingClientRect()}
    function fracAt(cx){var r=rect();return pv.a+clamp((cx-r.left-L)/(r.width-L-R),0,1)*span()}
    function scrubAt(cx){if(!route)return;scrubKm=fracAt(cx)*route.total/1000;scrubTxt();redraw()}
    function pts(){return Object.keys(ptr).map(function(k){return ptr[k]})}
    cv.addEventListener("wheel",function(e){if(!full&&!e.ctrlKey)return;e.preventDefault();zoomAt(fracAt(e.clientX),e.deltaY<0?.8:1.25)},{passive:false});
    cv.addEventListener("pointerdown",function(e){try{cv.setPointerCapture(e.pointerId)}catch(x){}
      ptr[e.pointerId]={x:e.clientX,y:e.clientY,x0:e.clientX};var p=pts();
      if(p.length===2){pinch={d:Math.abs(p[0].x-p[1].x)||1,mid:(p[0].x+p[1].x)/2,a:pv.a,b:pv.b};drag=null}
      else if(span()<0.999){drag={x:e.clientX,a:pv.a,moved:false}}
      else scrubAt(e.clientX)});
    cv.addEventListener("pointermove",function(e){
      if(!ptr[e.pointerId]){if(e.pointerType==="mouse")scrubAt(e.clientX);return}
      ptr[e.pointerId].x=e.clientX;var p=pts(),r=rect(),pw=r.width-L-R;
      if(pinch&&p.length>=2){var d=Math.abs(p[0].x-p[1].x)||1,mid=(p[0].x+p[1].x)/2,w0=pinch.b-pinch.a,w=clamp(w0*pinch.d/d,0.01,1),
        f0=pinch.a+clamp((pinch.mid-r.left-L)/pw,0,1)*w0,rel=clamp((mid-r.left-L)/pw,0,1);setView(f0-rel*w,f0-rel*w+w)}
      else if(drag){if(Math.abs(e.clientX-drag.x)>5)drag.moved=true;if(drag.moved){var w2=span(),a=drag.a-(e.clientX-drag.x)/pw*w2;setView(a,a+w2)}}
      else scrubAt(e.clientX)});
    function up(e){var q=ptr[e.pointerId];delete ptr[e.pointerId];if(pts().length<2)pinch=null;
      if(drag&&!drag.moved&&q)scrubAt(q.x);drag=null}
    cv.addEventListener("pointerup",up);cv.addEventListener("pointercancel",up);
  }
  attach(c2,false);attach(c3,true);
  function wireSb(id){var sb=$(id),d=null;
    sb.addEventListener("pointerdown",function(e){if(span()>=0.999)return;try{sb.setPointerCapture(e.pointerId)}catch(x){}
      var r=sb.getBoundingClientRect(),f=(e.clientX-r.left)/r.width,w=span();
      if(f<pv.a||f>pv.b)setView(f-w/2,f+w/2);d={x:e.clientX,a:pv.a}});
    sb.addEventListener("pointermove",function(e){if(!d)return;var r=sb.getBoundingClientRect(),w=span(),a=d.a+(e.clientX-d.x)/r.width;setView(a,a+w)});
    var up=function(){d=null};sb.addEventListener("pointerup",up);sb.addEventListener("pointercancel",up)}
  wireSb("sb2");wireSb("sb3");
  function mid(){return (pv.a+pv.b)/2}
  $("z2In").onclick=$("pfIn").onclick=function(){zoomAt(mid(),.5)};
  $("z2Out").onclick=$("pfOut").onclick=function(){zoomAt(mid(),2)};
  $("z2All").onclick=$("pfReset").onclick=function(){setView(0,1)};
  function open(){ov.hidden=false;document.body.style.overflow="hidden";scrubTxt();setTimeout(redraw,30)}
  function close(){ov.hidden=true;document.body.style.overflow="";drawCharts();sbUpd()}
  $("pFullBtn").onclick=open;$("pfClose").onclick=close;
  document.addEventListener("keydown",function(e){if(!ov.hidden&&e.key==="Escape")close()});
  window.addEventListener("resize",function(){if(!ov.hidden)redraw()});
  window.tccSbUpd=sbUpd;sbUpd();
})();

/* ================= alerts ================= */
var AC=null,swReg=null,bannerTimer=0;
function unlockAudio(){try{AC=AC||new (window.AudioContext||window.webkitAudioContext)();if(AC.state==="suspended")AC.resume()}catch(e){}}
document.addEventListener("pointerdown",unlockAudio,{once:true});
function beep(){if(!AC)return;try{[0,0.22].forEach(function(dt){var o=AC.createOscillator(),g=AC.createGain();o.type="sine";o.frequency.value=dt?1040:880;
  g.gain.setValueAtTime(0.0001,AC.currentTime+dt);g.gain.exponentialRampToValueAtTime(0.35,AC.currentTime+dt+0.02);g.gain.exponentialRampToValueAtTime(0.0001,AC.currentTime+dt+0.18);
  o.connect(g);g.connect(AC.destination);o.start(AC.currentTime+dt);o.stop(AC.currentTime+dt+0.2)})}catch(e){}}
function showBanner(text,keep){
  $("bannerText").textContent=text;$("banner").hidden=false;clearTimeout(bannerTimer);
  if(!keep)bannerTimer=setTimeout(function(){$("banner").hidden=true},14000);
}
$("bannerX").onclick=function(){$("banner").hidden=true};
function describe(ev,dist){
  if(ev.kind==="climb"){var s=ev.s;
    return "ทางขึ้นอีก "+dist+" ม. · "+s.cn+"/"+climbs.length+" · ชันเฉลี่ย "+s.avg.toFixed(0)+"% · +"+Math.round(s.gain)+" ม. · ยาว "+(s.len/1000).toFixed(1)+" กม."}
  return "ช่วงชันอีก "+dist+" ม. · "+ev.avg.toFixed(0)+"% · ยาว "+Math.round(ev.len)+" ม."}
function fire(text){
  showBanner(text,false);
  if(S.vib&&navigator.vibrate){try{navigator.vibrate([300,120,300,120,300])}catch(e){}}
  if(S.snd)beep();
  if(document.hidden&&swReg&&window.Notification&&Notification.permission==="granted"){
    try{swReg.showNotification("Trail Cutoff Clock",{body:text,tag:"hill",renotify:true,vibrate:[300,120,300]})}catch(e){}}
}
function checkAlerts(km){
  if(lastKm==null){lastKm=km;return}
  if(S.alertOn&&route){
    events.forEach(function(ev){
      var lead=(ev.kind==="pitch"?Math.min(S.lead,200):S.lead)/1000,trig=ev.start-lead;
      if(lastKm<trig&&km>=trig&&km<ev.end){fire(describe(ev,Math.max(0,Math.round((ev.start-km)*1000/10)*10)))}
    });
  }
  lastKm=km;
}
function hillLine(km){
  var el=$("hillLine");
  if(!route){el.textContent="";el.className="hillline";return}
  var i=idxAt(km),cur=null,nxt=null,x;
  for(x=0;x<climbs.length;x++){var s=climbs[x],a=s.a*route.step/1000,b=s.b*route.step/1000;
    if(km>=a-0.005&&km<=b){cur=s;break}if(a>km&&!nxt)nxt=s}
  if(cur){var left=Math.max(0,route.se[cur.b]-route.se[i]),dl=Math.max(0,(cur.b-i)*route.step/1000);
    el.className="hillline on";el.textContent="กำลังขึ้น "+cur.cn+"/"+climbs.length+" · เหลือ +"+Math.round(left)+" ม. อีก "+dl.toFixed(1)+" กม. · ชัน "+sgn(route.grade[i],0)+"%"}
  else if(nxt){el.className="hillline";el.textContent="ถัดไป ทางขึ้น "+nxt.cn+"/"+climbs.length+" · อีก "+(nxt.a*route.step/1000-km).toFixed(1)+" กม. · ชัน "+nxt.avg.toFixed(0)+"% · +"+Math.round(nxt.gain)+" ม. · ยาว "+(nxt.len/1000).toFixed(1)+" กม."}
  else{el.className="hillline";el.textContent=climbs.length?"ไม่มีทางขึ้นเหลือแล้ว":"ไม่พบทางขึ้นที่เข้าเงื่อนไข"}
}

/* ================= cutoff table + tick ================= */
function renderCps(){
  var tb=$("cpBody");tb.innerHTML="";
  cps.forEach(function(cp,i){
    var tr=document.createElement("tr");tr.id="cp"+i;
    tr.innerHTML='<td><input aria-label="ชื่อจุด"></td><td><input class="km mono" type="number" step="0.1" min="0" aria-label="กม."></td><td><input class="tm mono" type="time" aria-label="เวลา Cutoff"></td><td class="mono" data-left></td><td><span class="pill wait" data-st></span></td><td><button class="x" aria-label="ลบจุดนี้">×</button></td>';
    var ins=tr.getElementsByTagName("input");
    ins[0].value=cp.name;ins[1].value=cp.km;ins[2].value=cp.time;
    ins[0].oninput=function(){cp.name=ins[0].value;save();drawAll()};
    ins[1].oninput=function(){var v=parseFloat(ins[1].value);if(!isNaN(v)){cp.km=v;save();drawAll();tick()}};
    ins[2].oninput=function(){if(ins[2].value){cp.time=ins[2].value;save();tick()}};
    tr.querySelector(".x").onclick=function(){cps.splice(i,1);save();renderCps();drawAll();tick()};
    tb.appendChild(tr);
  });
}
function tick(){
  var now=nowMs(),d=new Date(now);
  $("clock").textContent=pad(d.getHours())+":"+pad(d.getMinutes())+":"+pad(d.getSeconds());
  var km=runnerKm();
  var sorted=cps.map(function(c,i){return {c:c,i:i}}).sort(function(a,b){return a.c.km-b.c.km}),nextI=-1;
  for(var q=0;q<sorted.length;q++){if(km<sorted[q].c.km-0.05){nextI=sorted[q].i;break}}
  var started=startTs!=null,elapsed=started?now-startTs:0;
  $("sElapsed").textContent=hms(elapsed);$("sKm").textContent=km.toFixed(1)+" กม.";
  $("sGrade").textContent=route?sgn(route.grade[idxAt(km)],0)+"%":"-";
  var cnt=$("count"),lab=$("cLabel"),dl=$("cDeadline"),btn=$("startBtn");
  cnt.className="count";btn.textContent=started?"วิ่งอยู่":"สตาร์ท";btn.disabled=started;
  $("startNote").textContent=started?("สตาร์ทเมื่อ "+hhmm(startTs)+" น. (นับ Cutoff จากเวลานี้)"):"กดสตาร์ทตอนปล่อยตัว ถ้ากดผิดไปที่แท็บตั้งค่าแล้วรีเซ็ต";
  cps.forEach(function(cp,i){
    var tr=$("cp"+i);if(!tr)return;
    var left=tr.querySelector("[data-left]"),st=tr.querySelector("[data-st]"),tm=tr.querySelector(".tm");
    if(document.activeElement!==tm)tm.value=cp.time;
    var passed=km>=cp.km-0.05;tr.className=(i===nextI)?"isnext":"";
    if(!started){left.textContent="-";st.className="pill wait";st.textContent="รอ";return}
    var ms=startTs+offsetMs(cp)-now;
    if(passed){left.textContent="";st.className="pill done";st.textContent="ผ่านแล้ว"}
    else if(ms<0){left.textContent=hms(ms);st.className="pill miss";st.textContent="เกินเวลา"}
    else{left.textContent=hms(ms);st.className="pill "+(i===nextI?"next":"wait");st.textContent=i===nextI?"ถัดไป":"รอ"}
  });
  if(!started){lab.textContent="ยังไม่สตาร์ท";dl.textContent="ปล่อยตัว "+planStart+" น.";cnt.textContent="--:--:--";$("sReq").textContent="-";$("sBuf").textContent="-";return}
  if(nextI<0){lab.textContent="ครบทุกจุดแล้ว";dl.textContent="";cnt.textContent=hms(elapsed);cnt.classList.add("ok");$("sReq").textContent="-";$("sBuf").textContent="-";return}
  var cp=cps[nextI],dead=startTs+offsetMs(cp),left2=dead-now,dist=cp.km-km;
  lab.textContent="ถึง "+cp.name+" · "+cp.km+" กม. (เหลือ "+Math.max(dist,0).toFixed(1)+")";
  dl.textContent="ปิด "+hhmm(dead)+" น.";cnt.textContent=hms(left2);
  $("sReq").textContent=left2>0&&dist>0?pace(left2/dist):"-";
  var bufMs=km>0.5&&elapsed>0?left2-dist*(elapsed/km):left2;
  $("sBuf").textContent=km>0.5&&elapsed>0?hms(bufMs):"-";
  cnt.classList.add(left2<0?"bad":(bufMs<0||left2<20*60000)?"warn":"ok");
}
function drawCharts(){if(window.tccSbUpd)window.tccSbUpd();drawProfile($("prof"),false);if(!$("p-hill").hidden)drawProfile($("prof2"),true);if(!$("pfull").hidden)drawProfile($("prof3"),true)}
function drawAll(){drawCharts();reqDraw()}
function onPos(){var km=runnerKm();checkAlerts(km);hillLine(km);if(follow)centerRunner();drawAll();tick();
  if(!$("p-hill").hidden)renderHills()}

/* ================= route UI ================= */
function setRoute(r,persist){
  route=r;selSeg=null;scrubKm=null;lastKm=null;pv.a=0;pv.b=1;buildEvents();
  var km=Math.floor(r.total/100)/10;$("simKm").max=Math.max(km,1);
  if(simKm>km){simKm=0;$("simKm").value=0;$("simKmV").textContent="0.0"}
  $("gTotal").textContent=(r.total/1000).toFixed(1)+" กม.";$("gGain").textContent=Math.round(r.gain)+" ม.";$("gMax").textContent=Math.round(r.max)+" ม.";
  if(persist){var ok=LS.set("tcc.route",JSON.stringify({name:r.name,pts:r.pts}));
    $("gpxMsg").className="msg";$("gpxMsg").textContent=(r.name?r.name+" · ":"")+(r.total/1000).toFixed(1)+" กม. "+(ok?"บันทึกไว้ใช้ออฟไลน์แล้ว":"โหลดแล้ว แต่บันทึกไว้ในเครื่องไม่ได้")}
  fitRoute();renderHills();updateTileEstimate();hillLine(runnerKm());drawAll();tick();
}
$("file").addEventListener("change",function(e){
  var f=e.target.files&&e.target.files[0];if(!f)return;
  var msg=$("gpxMsg");msg.className="msg";msg.textContent="กำลังอ่าน...";
  var fr=new FileReader();
  fr.onload=function(){try{setRoute(build(parseGpx(String(fr.result),f.name.replace(/\.gpx$/i,""))),true)}catch(err){msg.className="msg err";msg.textContent=err.message}};
  fr.onerror=function(){msg.className="msg err";msg.textContent="อ่านไฟล์ไม่สำเร็จ"};
  fr.readAsText(f);
});
$("sampleBtn").onclick=function(){setRoute(sampleRoute(),false);$("gpxMsg").className="msg";$("gpxMsg").textContent="ใช้เส้นทางตัวอย่าง ไม่ได้บันทึกไว้ในเครื่อง"};
var clearArm=false;
$("clearBtn").onclick=function(){var b=$("clearBtn");
  if(!clearArm){clearArm=true;b.textContent="กดอีกครั้งเพื่อยืนยัน";setTimeout(function(){clearArm=false;b.textContent="ล้างเส้นทางที่บันทึกไว้"},3000);return}
  clearArm=false;b.textContent="ล้างเส้นทางที่บันทึกไว้";LS.del("tcc.route");setRoute(sampleRoute(),false);$("gpxMsg").textContent="ล้างแล้ว กลับไปใช้เส้นทางตัวอย่าง"};

/* ================= start / inputs ================= */
$("startBtn").onclick=function(){unlockAudio();if(startTs==null){startTs=nowMs();save();tick()}};
var rstArm=false;
$("resetBtn").onclick=function(){var b=$("resetBtn");
  if(!rstArm){rstArm=true;b.textContent="กดอีกครั้งเพื่อยืนยัน";setTimeout(function(){rstArm=false;b.textContent="รีเซ็ตการสตาร์ท"},3000);return}
  rstArm=false;b.textContent="รีเซ็ตการสตาร์ท";startTs=null;save();tick()};
$("planStart").oninput=function(e){if(e.target.value){planStart=e.target.value;save();tick()}};
$("addCp").onclick=function(){var last=cps[cps.length-1];cps.push({name:"CP"+(cps.length+1),km:last?last.km:0,time:last?last.time:"12:00"});save();renderCps();tick()};
$("simKm").oninput=function(e){simKm=parseFloat(e.target.value)||0;$("simKmV").textContent=simKm.toFixed(1);save();onPos()};
$("shift").oninput=function(e){shiftH=parseFloat(e.target.value)||0;$("shiftV").textContent=shiftH.toFixed(1);save();tick()};

/* alert settings */
function readSettings(){
  S.alertOn=$("aOn").checked;S.vib=$("aVib").checked;S.snd=$("aSnd").checked;
  S.lead=clamp(parseInt($("aLead").value)||300,50,2000);S.minGain=clamp(parseInt($("aGain").value)||30,5,500);S.steep=clamp(parseInt($("aSteep").value)||12,5,40);S.offOn=$("aOff").checked;S.offDist=clamp(parseInt($("aOffD").value)||50,20,500);
  save();buildEvents();renderHills();hillLine(runnerKm());drawAll();
}
["aOn","aVib","aSnd","aLead","aGain","aSteep","aOff","aOffD"].forEach(function(id){$(id).addEventListener("change",readSettings)});
$("aTest").onclick=function(){unlockAudio();var ev=events[0];
  fire(ev?describe(ev,S.lead):"ทางขึ้นอีก "+S.lead+" ม. · ชันเฉลี่ย 9% · +120 ม. · ยาว 1.4 กม. (ข้อความทดสอบ)")};
$("aNotif").onclick=function(){
  var m=$("aNote");
  if(!window.Notification){m.textContent="เบราว์เซอร์นี้ไม่รองรับแจ้งเตือนของระบบ (บน iPhone ต้องติดตั้งลงหน้าโฮมก่อน)";return}
  Notification.requestPermission().then(function(p){m.textContent=p==="granted"?"เปิดแจ้งเตือนของระบบแล้ว จะแสดงเมื่อแอปอยู่เบื้องหลัง":"ไม่ได้รับอนุญาต เปิดได้ที่การตั้งค่าเบราว์เซอร์หรือแอป"})};

/* ================= GPS ================= */
var ARR=["↑","↗","→","↘","↓","↙","←","↖"],DIR=["เหนือ","ตะวันออกเฉียงเหนือ","ตะวันออก","ตะวันออกเฉียงใต้","ใต้","ตะวันตกเฉียงใต้","ตะวันตก","ตะวันตกเฉียงเหนือ"];
function nearestIn(lat,lon,i0,i1){
  var best=1e18,bi=i0,kx=Math.cos(lat*Math.PI/180);
  for(var i=i0;i<=i1;i++){var dx=(route.lon[i]-lon)*kx,dy=route.lat[i]-lat,d=dx*dx+dy*dy;if(d<best){best=d;bi=i}}
  return {i:bi,km:bi*route.step/1000,off:Math.sqrt(best)*111320};
}
function dirTxt(lat,lon,i){
  var dy=route.lat[i]-lat,dx=(route.lon[i]-lon)*Math.cos(lat*Math.PI/180),a=(Math.atan2(dx,dy)*180/Math.PI+360)%360,k=Math.round(a/45)%8;
  return ARR[k]+" "+DIR[k];
}
function merc(lat){var r=lat*Math.PI/180;return (1-Math.log(Math.tan(r)+1/Math.cos(r))/Math.PI)/2}
function saveTrail(){LS.set("tcc.trail",JSON.stringify(trail.map(function(q){return [Math.round(q[0]*1e6)/1e6,Math.round(q[1]*1e6)/1e6]})))}
function loadTrail(){var r=LS.get("tcc.trail");if(!r)return;try{trail=JSON.parse(r).map(function(q){return [q[0],q[1],(q[1]+180)/360,merc(q[0])]})}catch(e){trail=[]}}
function showOff(){
  var el=$("offLine");
  if(!offRoute||!gpsFix){el.hidden=true;return}
  el.hidden=false;
  el.textContent="ออกนอกเส้นทาง "+Math.round(gpsFix.off)+" ม. · ทางกลับอยู่ทาง "+dirTxt(gpsFix.lat,gpsFix.lon,gpsFix.ni)+" (เส้นทาง กม. "+(gpsFix.ni*route.step/1000).toFixed(1)+")";
}
function onFix(p){
  if(!route)return;
  var lat=p.coords.latitude,lon=p.coords.longitude,acc=p.coords.accuracy||0,t=Date.now(),m=$("gpsMsg");
  var thr=Math.max(S.offDist,acc),res=null,tgt;
  if(gpsKm==null){
    tgt=nearestIn(lat,lon,0,route.n);if(tgt.off<=thr)res=tgt;
  }else{
    // หาตำแหน่งในช่วงใกล้ความคืบหน้าเดิมก่อน กันกระโดดไปเส้นที่ซ้อนกัน
    var dt=gpsFix?Math.max(1,(t-gpsFix.t)/1000):1;
    var back=idxAt(Math.max(0,gpsKm-0.25)),fwd=idxAt(gpsKm+Math.max(0.8,dt/3600*20));
    var w=nearestIn(lat,lon,back,fwd);
    if(w.off<=thr){res=w;reloc=null;tgt=w}
    else{
      tgt=nearestIn(lat,lon,idxAt(Math.max(0,gpsKm-0.5)),idxAt(gpsKm+3)); // จุดกลับ: บริเวณที่ออกจากเส้น
      var g=nearestIn(lat,lon,0,route.n);
      if(g.off<=thr){ // กลับเข้ามาที่จุดอื่นของเส้นทาง ต้องเจอซ้ำ 3 ครั้งถึงย้ายตำแหน่ง
        if(reloc&&Math.abs(reloc.km-g.km)<0.3)reloc.n++;else reloc={km:g.km,n:1};
        if(reloc.n>=3){res=g;tgt=g;reloc=null}
      }else reloc=null;
    }
  }
  gpsFix={lat:lat,lon:lon,acc:acc,t:t,u:(lon+180)/360,v:merc(lat),off:tgt.off,ni:tgt.i};
  if(res){
    gpsKm=res.km;offFixes=0;
    if(offRoute){offRoute=false;showBanner("กลับเข้าเส้นทางแล้ว",false);if(S.vib&&navigator.vibrate){try{navigator.vibrate(200)}catch(e){}}}
    m.className="msg";m.textContent="จับสัญญาณแล้ว · บนเส้นทาง (ห่าง "+Math.round(res.off)+" ม.) ±"+Math.round(acc)+" ม.";
  }else{
    offFixes++;
    if(gpsKm!=null&&offFixes>=2){
      var txt="ออกนอกเส้นทาง "+Math.round(tgt.off)+" ม. · ทางกลับอยู่ทาง "+dirTxt(lat,lon,tgt.i);
      if(!offRoute){offRoute=true;lastOffAlert=t;if(S.offOn)fire(txt)}
      else if(S.offOn&&t-lastOffAlert>60000){lastOffAlert=t;fire(txt)}
    }
    m.className="msg err";m.textContent=(gpsKm!=null?"ออกนอกเส้นทาง ":"ยังไม่อยู่บนเส้นทาง ห่าง ")+Math.round(tgt.off)+" ม. ±"+Math.round(acc)+" ม.";
  }
  // รอยทางที่เดินจริง (บันทึกเมื่อขยับเกิน 8 ม.)
  var last=trail[trail.length-1];
  if(!last||hav(last[0],last[1],lat,lon)>8){
    trail.push([lat,lon,gpsFix.u,gpsFix.v,gpsFix.ni]);if(trail.length>4000)trail.splice(0,1000);
    if(trail.length-trailSaved>=15){trailSaved=trail.length;saveTrail()}
  }
  showOff();onPos();
}
function stopGps(msg,isErr){
  if(gpsWatch!=null){try{navigator.geolocation.clearWatch(gpsWatch)}catch(e){}}
  gpsWatch=null;gpsKm=null;gpsFix=null;offRoute=false;offFixes=0;reloc=null;saveTrail();
  $("gpsBtn").setAttribute("aria-pressed","false");$("offLine").hidden=true;
  var m=$("gpsMsg");m.className="msg"+(isErr?" err":"");m.textContent=msg;onPos();
}
$("gpsBtn").onclick=function(){
  var b=$("gpsBtn"),m=$("gpsMsg");
  if(gpsWatch!=null){navigator.geolocation.clearWatch(gpsWatch);stopGps("ปิดแล้ว",false);return}
  if(!navigator.geolocation){m.className="msg err";m.textContent="อุปกรณ์นี้ไม่รองรับ GPS ในเบราว์เซอร์";return}
  if(!route){m.className="msg err";m.textContent="อัปโหลด GPX ก่อน";return}
  m.className="msg";m.textContent="กำลังหาสัญญาณ...";b.setAttribute("aria-pressed","true");
  try{
    gpsWatch=navigator.geolocation.watchPosition(onFix,function(err){
      if(err&&err.code===1)stopGps("ใช้ GPS ไม่ได้ (ไม่ได้รับอนุญาตตำแหน่ง) ใช้ตัวเลื่อนทดลองแทน",true);
      else{m.className="msg err";m.textContent="ยังไม่พบสัญญาณ GPS รอสักครู่..."}
    },{enableHighAccuracy:true,maximumAge:3000,timeout:30000});
  }catch(e){stopGps("ใช้ GPS ไม่ได้ในหน้านี้",true)}
};
var trArm=false;
$("trClear").onclick=function(){var b=$("trClear");
  if(!trArm){trArm=true;b.textContent="กดอีกครั้งเพื่อยืนยัน";setTimeout(function(){trArm=false;b.textContent="ล้างรอยทางที่เดิน"},3000);return}
  trArm=false;b.textContent="ล้างรอยทางที่เดิน";trail=[];trailSaved=0;LS.del("tcc.trail");reqDraw()};

/* ================= wake lock ================= */
var wl=null;
$("wakeBtn").onclick=async function(){
  var b=$("wakeBtn");
  if(wl){try{await wl.release()}catch(e){}wl=null;b.setAttribute("aria-pressed","false");b.textContent="เปิดจอค้าง";return}
  try{wl=await navigator.wakeLock.request("screen");b.setAttribute("aria-pressed","true");b.textContent="จอค้างอยู่";
    wl.addEventListener("release",function(){wl=null;b.setAttribute("aria-pressed","false");b.textContent="เปิดจอค้าง"})}
  catch(e){b.textContent="เปิดจอค้างไม่ได้";setTimeout(function(){b.textContent="เปิดจอค้าง"},2500)}
};
document.addEventListener("visibilitychange",function(){
  if(document.visibilityState==="visible"&&$("wakeBtn").getAttribute("aria-pressed")==="true"&&!wl){$("wakeBtn").click();$("wakeBtn").click()}});

/* ================= offline map download ================= */
var dlBusy=false,dlCancel=false;
function isOsm(u){return !u||/openstreetmap\.org/i.test(u)}
function tileList(zmin,zmax){
  var set=new Set(),z,i,dx,dy;
  if(!route)return [];
  for(z=zmin;z<=zmax;z++){var n=Math.pow(2,z);
    for(i=0;i<=route.n;i+=5){var tx=Math.floor(route.mu[i]*n),ty=Math.floor(route.mv[i]*n);
      for(dx=-1;dx<=1;dx++)for(dy=-1;dy<=1;dy++){var x=tx+dx,y=ty+dy;if(y>=0&&y<n)set.add(z+"/"+(((x%n)+n)%n)+"/"+y)}}}
  return Array.from(set);
}
function updateTileEstimate(){
  var zmax=parseInt($("tZ").value)||15,cnt=route?tileList(11,zmax).length:0;
  $("tCount").textContent=route?cnt.toLocaleString():"-";
  var osm=isOsm(S.tileUrl),btn=$("tGo");btn.disabled=osm||cnt>6000;
  if(!dlBusy){$("tMsg").className="msg";$("tMsg").textContent=osm?"ใช้ OpenStreetMap: เก็บเฉพาะส่วนที่คุณเลื่อนดู โหลดล่วงหน้าไม่ได้":(cnt>6000?"ไทล์เยอะเกิน ลดระดับซูมสูงสุด":"")}
  countHave();
}
function countHave(){
  if(!window.caches){$("tHave").textContent="-";return}
  caches.open(TILE_CACHE).then(function(c){return c.keys()}).then(function(k){$("tHave").textContent=k.length.toLocaleString()}).catch(function(){$("tHave").textContent="-"});
}
$("tUrl").addEventListener("change",function(){S.tileUrl=$("tUrl").value.trim();tileCache.clear();save();updateTileEstimate();reqDraw()});
$("tAttr").addEventListener("change",function(){S.tileAttr=$("tAttr").value.trim();save();reqDraw()});
$("tZ").addEventListener("change",updateTileEstimate);
async function runDownload(list,urlFn,b,label){
  var m=$("tMsg"),done=0,fail=0,i=0;
  if(dlBusy){dlCancel=true;return}
  if(!window.caches||!route)return;
  dlBusy=true;dlCancel=false;b.textContent="ยกเลิก";m.className="msg";
  try{
    var cache=await caches.open(TILE_CACHE);
    async function worker(){
      while(i<list.length&&!dlCancel){
        var key=list[i++],p=key.split("/"),url=urlFn(p[0],p[1],p[2]);
        try{var req=new Request(url,{mode:"cors"});
          if(!(await cache.match(req))){var res=await fetch(req);if(res.ok)await cache.put(req,res);else fail++}}
        catch(e){fail++}
        done++;if(done%10===0||done===list.length)m.textContent="โหลดแล้ว "+done+"/"+list.length+(fail?" · พลาด "+fail:"");
      }
    }
    await Promise.all([worker(),worker(),worker(),worker(),worker(),worker()]);
    m.textContent=(dlCancel?"หยุดแล้ว ":"เสร็จแล้ว ")+done+"/"+list.length+(fail?" · พลาด "+fail+" (ตรวจลิงก์)":"");
  }catch(e){m.className="msg err";m.textContent="โหลดไม่สำเร็จ: "+e.message}
  dlBusy=false;dlCancel=false;b.textContent=label;countHave();reqDraw();
}
$("tGo").onclick=function(){if(isOsm(S.tileUrl)&&!dlBusy)return;runDownload(tileList(11,parseInt($("tZ").value)||15),tileUrl,$("tGo"),"โหลดแผนที่ตามเส้นทาง")};
$("tDem").onclick=function(){runDownload(tileList(10,13),demUrl,$("tDem"),"โหลดข้อมูลความสูง 3D ล่วงหน้า")};
$("sUrl").addEventListener("change",function(){S.satUrl=$("sUrl").value.trim();save();reqDraw()});
$("sAttr").addEventListener("change",function(){S.satAttr=$("sAttr").value.trim();save();reqDraw()});
$("dUrl").addEventListener("change",function(){S.demUrl=$("dUrl").value.trim();save();reqDraw()});
var tcArm=false;
$("tClear").onclick=function(){var b=$("tClear");
  if(!tcArm){tcArm=true;b.textContent="กดอีกครั้งเพื่อยืนยัน";setTimeout(function(){tcArm=false;b.textContent="ล้างแผนที่ในเครื่อง"},3000);return}
  tcArm=false;b.textContent="ล้างแผนที่ในเครื่อง";
  if(window.caches)caches.delete(TILE_CACHE).then(function(){tileCache.clear();countHave();reqDraw()});
};


/* ================= กลุ่มวิ่ง (Firebase Realtime Database ผ่าน REST ไม่ต้องล็อกอิน) ================= */
var grp={on:false,room:"",name:"",friends:[],sentLocal:0,offset:0,lastOk:0,lastTry:0,lastFix:0,pushErr:"",pollErr:"",timer:0,busy:false,routeKey:"",routeTried:0,avKey:"",myColor:"",trails:{}};
var FCOL=["#d91e36","#2e9e44","#8e24aa","#00a6a6","#f2b600","#e91e8c","#795548","#7cb518","#455a64","#ff6d00","#1e88e5","#6a1b9a"];
var GRULES="{\n  \"rules\": {\n    \"rooms\": {\n      \"$room\": {\n        \".read\": true,\n        \"$uid\": {\n          \".write\": true,\n          \".validate\": \"newData.hasChildren(['n','la','lo','s']) && newData.child('n').isString() && newData.child('n').val().length <= 24 && newData.child('la').isNumber() && newData.child('lo').isNumber()\"\n        }\n      }\n    },\n    \"routes\": {\n      \"$room\": {\n        \".read\": true,\n        \".write\": true,\n        \".validate\": \"newData.hasChildren(['p','h']) && newData.child('p').isString() && newData.child('p').val().length < 90000\"\n      }\n    },\n    \"avatars\": {\n      \"$room\": {\n        \".read\": true,\n        \"$uid\": {\n          \".write\": true,\n          \".validate\": \"newData.isString() && newData.val().length < 3200\"\n        }\n      }\n    }\n  }\n}";
function myUid(){var u=LS.get("tcc.uid");if(!u){u=Math.random().toString(36).slice(2,10)+Date.now().toString(36).slice(-4);LS.set("tcc.uid",u)}return u}
function fbBase(){var u=(S.fbUrl||(window.TCC_CONFIG&&window.TCC_CONFIG.fbUrl)||"").trim();return u.replace(/\/+$/,"")}
function colorOf(id){var h=0;for(var i=0;i<id.length;i++)h=(h*31+id.charCodeAt(i))>>>0;return FCOL[h%FCOL.length]}
function assignColors(ids){var map={},used={},list=ids.slice().sort();
  list.forEach(function(id){var h=0;for(var i=0;i<id.length;i++)h=(h*31+id.charCodeAt(i))>>>0;var k=h%FCOL.length,t=0;while(used[k]&&t<FCOL.length){k=(k+1)%FCOL.length;t++}used[k]=1;map[id]=FCOL[k]});
  return map}
function initial(n){return String(n||"?").trim().charAt(0).toUpperCase()||"?"}
function ageTxt(ms){ms=Math.max(0,ms);var s=Math.round(ms/1000);if(s<60)return s+" วิ";var m=Math.round(s/60);if(m<60)return m+" นาที";return Math.floor(m/60)+" ชม. "+(m%60)+" น."}
function fetchT(url,opt,ms){var ac=window.AbortController?new AbortController():null,t=setTimeout(function(){if(ac)ac.abort()},ms||8000);
  opt=opt||{};if(ac)opt.signal=ac.signal;return fetch(url,opt).finally(function(){clearTimeout(t)})}
function roomOk(r){return /^[A-Z0-9]{4,12}$/.test(r)}

/* ===== ตัวละคร 16 บิต (สไตล์ SNES ประมาณ 32x48 พิกเซล) ===== */
var SPR=[{"n":"นักวิ่ง","cu":"131e49182f650384a527305b7f45211c2b65234a7e67888eb6a387009fc800a2cc00bbeb04b1dd3aadc7c3c3c3e03102fb3f01fe4d04e16f42d99671f0b787f3c79bffc8921b1b2f|32x48|z9x11z19x2r3q5r1p2x3z15x1r7q5p4x2z12x1r8q7p4x1z10x1r1q1r7q8p3x1z10x1q3r4q10p4x1z9x1q17p4x1z9x1r1q16p4x1z8x2q16p4x3z6x1p2e3p10q1r9x1z5x1p2e3p10r11x1z4x1r1q1e3p1r19x1z6x2e3t1u1i1e1w6t1e1s1t1s4x2z8x1e3t1i1h1a1t1w5h1d1e1u1t4x1z9x1e3u1i1a2t1w5e1a1e1u1t3x1z10x1w4u1e2w6i1e1i1u1t3x1z11x1w2u2w11t4x1z11x1w2t2u1w9u1t4x1z11x1w3u1w10u1t3x1z13x1w6t1s3u1w1u1t4x1z14x1w5t4u1w1t4x1z16x1w9u1t3x1z18x1v1w5u1t3i1x1z14x5k1m1n1o1i1u1t1i2h1c3x5z8x1m2j1c1j1k1l4k1j5c2j1m1k1j1c1x1z6x1k1l2j3k1l4k1j5c2j1l1k1j1c1x1z6x1j1l2j3k1l4k1j5c2j1l1k1j1c1x1z6x1j1l2j3k1l4k1j5c2j1l1k1j1c1x1z6x1j1m2j3k1m1l2m1k1j5c2j1l1k1j1c1x1z6x1j1k2j5k2j7c3k1j2c1x1z6x1j17c3j3c1x1z6x1j17c3j3c1x1z6x1j17c3j3c1x1z6x1j1n1o1v1h1j12c2n1o1v1i1n1x1z7x1v1w3n1j11c2h1w3v1x1z7x1w4h1g1b4g1c1g1b4c1i1w4x1z7x1w4x1f5a1g1f4a1d1x1w3x1z9x5f5a1x1f4a1d1x4z14x1f5a1x1f4a1d1x1z17x1f5a1x1f4a1d1x1z17x1f5a1x1f4a1d1x1z17x1f5a1x1f4a1d1x1z17x1f4g1d1x1f4g2x1z18x5o1x5o2x1z22x1o1x1z4x1o1x1z19x4o1x1z1x4o1x1z18x1o5x2o5x1z19x5z2x5z10"},{"n":"นินจา","cu":"141422151830191d3a1f2448252745282c574f2239302d4e4741537b4449d308089777689a7e71c19979de1317f71111ff1715ff2a24ee594ce8b78bf8c290ffc892ffc8921b1b2f|32x48|z9x8z22x2f3e1d2h1e1x2z19x1i1f3d5c2e1x1z18x1f5d5c3x1z16x1f6d6c3x1z6x1z7x1f7d7c3x1z4x1r1x1z6x1d1f7d6c3e1x1z1x2q1p1x1z5x1f1d1f6d8c3x2q1p2q1x1z4x1r1o19p5q1x1z4x1r1p24q1x1z4x1r20o1k1o1q1x2z6x1n1v3t1n1t1v6t1n1t1v3l1k3o1x1z6x1n1v3m1i1l1v6m1i1l1v3m1j1k3o1x1z5x1n1v3j1a1l1v6i1a1l1v3m1x1o1k1o1x1z6x1n1v3n1i1n1v6m1i1n1v3m1x4z7x1m1v17u1l1x1z10x1i1l1m13l3i1e1x1z11x1d14c4x1z12x1f1d13c3h1x1z13x1d12c4x1z14x1h1d11c3x1z16x1i1d9c2e1x1z18x1h1d6c4e1x1z13x5d3f1d2c4d1c1b1c1x5z7x1f1d3c1d2f3d6c1b2d3c1h1x1z6x1d1f1d2c1d2f3d6c1b2d4e1x1z6x1d1f1d2c1d2f3d6c1b2d4e1x1z6x1d1f1d2c1d2f3d6c1b2d4e1x1z6x1d4e1g14d4e1x1z6x1d4g1p14g1d3e1x1z6x1d4g1p14g1d3e1x1z6x1d4c1e12b2c1d3e1x1z6x1d2h1e1c1d11c1b2c1h2d1e1x1z6x1i1n1v1t1i1d11c1b2l1t1u1n1i1x1z6x1t1v3m1d11c1b2n1v3t1x1z6x1v4t1e1c4b1c5b1a1i1u1v4x1z7x1v3x2c1d1c2b2e1d1c3a1x1v4x1z9x3z1x1c1d1c2b1a1h1d1c3a1x5z14x1c1d1c2b1a1h1c4a1x1z18x1c4b1a1e1c4a1x1z18x1c4b1a1e1c4a1x1z18x1c4b1a1e1c4a1x1z18x1b4a2e1b4a1x1z17x1e1a5b1c1a6x1z16x1a6e1a7x1z16x1a6e1a7x1z17x1a1b4x2b4a1x1z19x5z2x5z12"},{"n":"หุ่นยนต์","cu":"111e3a25334c384a5e4c556a5c687f536d875e6b8765718b707a8d4a849c717d957782974babbd39d9e32efcff7e8aa3808ca1ff2f2f89889b919eb495a3b898a5baaab9d21b1b2f|32x48|z13x4z27x1r4x1z26x1r5x1z25x1r4x1z19x9s1i1x10z10x1v1u1v1w4v1u7t1q1i3l1x1z9x1u2w6v1u8l1i3x1z8x1u3w7u8q1i3x1z8x1u3w7u8q1i3x1z8x1u3w7u8q1i3x1z8x1u3w2v4u1q8l1i3x1z8x1u3q1b1a13b1g1i2x1z8x1u3d1a2j1n1m1b1a3c1n2j1a2d1i2x1z8x1u3d1a1j1o3j1a3n1o3c1a1d1i2x1z8x1u3d1a1j1o3m1a3n1o3j1a1d1i2x1z8x1u3d1a1c1o3j1a3m1o3b1a1d1i2x1z8x1u3d1a2j1n1j1a4b1m1n1c1a2d1i2x1z8x1u3d1a15d1i2x1z8x1u3q1c1b13c1h1i2x1z8x1u18q1i3x1z8x1u8t1l5t1u3q1i3x1z8x1u8e1b5i1u3q1i3x1z8x1t1u7q1i5q1u3q1i3x1z9x1t1u15t1i4x1z9x1t1q5t3q6k1i1l1q3x1z8x1v1w1v1t1p2u1v3t1p5e2t1w1u1t1l1x1z7x1w2v1u1p2v4u1m1p4e2t1w1u1t1l1x1z7x1w2v1u1p2v3n1o3m1p2e2t1w1u1t1l1x1z7x1w2v1u1p2t1v2o4n1p2e2t1w1u1t1l1x1z7x1v1w1u2p3t2n1o3n1p2e2t1w1u1t1l1x1z7x1u4p5m1n1o1n1p3e2q1u2t1l1x1z7x1u4p12e2q1u2t1l1x1z7x1u4p3k1h7k1e2q1u2t1l1x1z7x1u4p3i1e7i1e2q1u2t1l1x1z7x1u4q1p11e2q1u3q1x1z7x1u4q1l1k4i1p1k3h1e2q1u3v1x1z7x1v1u4h1k2g2d1h2k1g2d1e1v1u3x1z9x2v1x2g1k2g2d1h1k1l1h1g1d1x3v1x1z12x1z1x1g1k2g2d1h1k2h1g1d1x1z2x1z15x1g1h2g2d1h1g1h1g2d1x1z18x1g5d1h1g4d1x1z18x1g5d1h1g4d1x1z18x1g1e4d1h1g1e3d1x1z18x1e1d3c2d5c2x1z17x1d5c1d5c2x1z17x1d5c1d5c2x1z17x1d4c2x1d4c2x1z18x6z1x6z10"},{"n":"แมว","cu":"d87c00ea8600fb9a01ffa701523506996304db8903f19c02ffa502ffab03ffc707796136d38a22d89435e48c0ee9a848fea31bffb017f4b874d2c0b0f5d891eae6d3fffce61b1b2f|32x48|z5x1z17x1z12x1r1x2z13x2r1x1z11x1j1d1j1x1z2x5z3x2r1d2x1z11x1j1q2j1x2r1d1i1h1o1x3r1j1q2r1x1z11x1r1q1s1k3j1d3i1b1g1o1h1p1s1q1j1x1z11x1j1q1k5d5h1a2n1s1p1j1x1z11x1d1k6j1d5h1a2o1q1j1x1z11x1d1k7d6h1a2g1c1x1z11x1d1k7d6i1g1a2b1x1z10x1r1d1k7d7h1a3x1z10x1j1d1k6j1d7i1a3g1x1z9x1d2j1k5j1d8b1a3x1z8x1r1d3j1n1l1g1j1d6m1l1a1b1a3x1z8x1j1d4l2f1d7l2f1h1a3o1x1z7x1d5e2f1d7e2f1h1a3o1x1z7x1r1d4a1f1a1d7a1f1a1b1a3o1x1z8x1d2h3i1d3i3d4i1a4x1z9x1d3i1h3c1d1q1s1q1d1h4a4x1z9x1j1d8q1p1q1d4c1a3g1x1z10x1d1i1h4c1d5h3g1a3x1z11x1j1c1h1d11c1a3o1x1z12x1j1d11i1b1a2o1x1z14x1j1d9i1b1a2o1x1z13x4d8i1b1a2g1x4z10x1j1i1h1q1d1j2d2i1c1b1a2b1a2o1j1i1h1x1z8x1j1k1j1i1h1d1k1u3s5p1o1a1h1k1j1i1o1x1z7x1j1k1j1d1h1d1u1w7v1t1p1a1h1k1j1d1o1x1z7x1j1k1j1d1h1d1u1w7v1t1p1a1h1k1j1d1o1x1z7x1j1k1j1d1h1d1u1w7v1t1p1a1h1k1j1d1h1i1x1z6x1j2d2h1d1u1w7v1t1p1a1h1j1d5x1z5x1d4h1d1u1w7v1t1p1a1b1d6r1x1z4x1d4h1d1u1w7v1t1p1a1b1d6r1x1z4x1d4h1d1u1w7v1t1p1a1b1d6r1x1z4x1i1d3h1d1s1w7v1t1p1a1b1d6r1x1z4x1i1d3i1d1r1p1s6p2g1a1b1d6r1x1z4x1r1d3c6b1i1c4a2h1d6r1x1z4x1r1d3j1c1i2c2a1o1c1j1c2b1p1s1d6r1x1z5x2r1x2c1d2c2a1x1c1j1c2b1p1r1d6x1z8x1z1x1c1d2c2a1x1c1j1c2b2d7r1x1z9x1c5a1x1c4b1o1j1d5j1x1z10x1c5a1x1c4b1a1x3r1x3z11x1c5a1x1c4b1a1x1z2x1z14x1c4q1a1x1c4o1m1x1z18x5t1x6t1x1z22x1t1x1z4x1t1x1z22x1t1x1z4x1t1x1z21x1v1t1x1z3x1t2x1z22x2z5x2z11"},{"n":"เอเลี่ยน","cu":"02091608161e21543c32ac523bc55c47f2705157754fa3774ced754df67755647d55f48057ff875a767f58fc8557ff875e768890c965fffe197484a893a1ca8cacc09fafda1b1b2f|32x48|z8x2z11x3z15x1s2x1z9x1s3x1z14x1s2x11r1s2x1z15x2l2j1f3i1e3x4z15x1m4j1f5e4x1z15x1m6j1f6e3x1z14x1m6o1f7e3x1z12x1j1m7f7e4x1z10x1l1j1m7j1f7e4x1z9x1j2m7f8e5x1z8x1f2m6o1f9e2d1e1x1z7x1j1f1c2d1e1o1m2j1f8d1c3e1x1z7x1j1f1b1a3b1c1d2f4d1c2b1a3c1e1x1z7x1j1f1c1a1b1w1b1a2c1f3e1b1a2v1c1a2c1e2x1z6x1f2c1a1b1g1b1a2c1f4c1a2g1b1a2c1e2x1z6x1j1f1d1a6d1f4c1a6d1e2x1z6x1l1f1d1a5b1e1f4d1a6d1e2x1z6x1j1f1d1a5c1f5e1b1a4b1d1e1x1z7x1l1f1e1b1a4c1f6c1a4b1d1e1x1z8x1j1f1e1d1c1a2d1f6c1a2c2d1e2x1z8x1l1f4d1c1e1f6d1c1e5x1z10x1f15e5x1z10x1j1f7e1d2f4e4x1z12x1l1f12e4x1z12x3i2f9e3h1x4z9x1o1j1f1e1v1l2f5e3h1q1t1o1j1f1e1x1z7x1j1m1l1f1i1u1w3v2h3t1v1t3m1j1f1e1x1z7x1j1m1l1f1i1u1w5u5t3m1j1f1e1x1z7x1j1m1l1f1i1u1w5u5t3m1j1f1e1x1z7x1f1j2f1i1u2w3u6t3l1j1f1e1x1z7x1f4i1u11t3f3e1x1z7x1f4i1u11t3f3e1x1z7x1f4i1u11t3f3e1x1z7x1f4i1u11t3f3e1x1z7x1i1f3i1u11t3f4x1z7x1o1f3i1v1u2t3u4t2q1h1f4x1z8x1j1f3x1t1u1t2q2t1u1t3q1x1j1f2j1x1z9x1l2x2t1u1t2q1k1t1u1t3q1x2l1x2z11x2z1x1t1u1t2q1k1t1u1t3q1x1z1x1z16x1t4q1k1t5q1x1z18x1t4q1k1t5q1x1z18x1t4q1k1t5q1x1z18x1t4q1k1t4q1k1x1z18x1k2g4k3g3x1z17x1g1k1q1k1g3k1q1k1g3x1z17x1g7k1g5x1z18x1g5x1g6x1z19x5z1x6z10"},{"n":"อัศวิน","cu":"0d11221f2435555c6e71788d8794a21d49bd2257e8255ef45575be4272e78e99aa8698c2fb1826c2647393a1a896a1b197a4bdfae129a6af99a0aec6a8b5cdb8c7ddc6d4e81b1b2f|32x48|z16x4z27x1m4x1z25x1m6x1z18x7m6x5z13x1v3w3v7u1p1k2o1x1z11x1v3w5v7u1k3x1z11x1v2w7v7p1k2p1x1z10x1v2w7v7q1k2p1x1z10x1v2w7v7q1k2p1x1z10x1v2w7v7q1k2p1x1z10x1v2w6u1v1u1t5e2k1p1x1z10x1v1u1b1a6q1c1a6c1k1p1x1z10x1v1t1a7q1c1a6b1k1p1x1z10x1v1t1a7q1c1a6b1k1p1x1z10x1v1t1a7q1c1a6b1k1p1x1z10x1v1t1a7q1c1a6b1k1p1x1z10x1v2c1b6t1d1b6c1k1p1x1z10x1v16q1k2p1x1z10x1v3u13p1k2p1x1z10x1v3e14k2p1x1z10x1v4k2v2u1k1p1v2u1k1p1q1k2p1x1z10x1v3u1c2u1v1q1c2v2q1c2q1k2p1x1z10x1v4q1t1v3q1t1v3q1t1p1k2p1x1z10x1u1v14t1k3x1z11x2q2u1q1l9i1e1p1q1t1x2z9x1v1u1t1p1v1j1h3i1e2j1h1g1f1i1p1v1u1t1e1x1z6x2j1l2t1q1u1h4s1r2i1h1g1f2p1w1u1t1e1x1z5x1h4g1i1q1u1h4s1r2i1h1g1f2p1w1u1t1e1x1z5x1h4g1f1q1u1h4s1r2i1h1g1f2p1w1u1t1e1x1z5x1h2i2g1f1l2h4s1r2i1h1g1f2l1v1u1t1e1x1z5x1h2o1e1g1f1l1g1h4s1r2i1h1g1f2j1t3e1x1z5x1h2o1e1g1f1l1j1h4s1r2i1h1g1f2i1t3e1x1z5x1h2o1e1g1f1l1v1g1h3e1s2i1h1f3p1t3e1x1z5x1h2e2g1f1l1v1l1i10e1p1u3e1x1z5x1h2e2g1f1u1v11t1k1p1v3t1x1z5x1h2e2g1f1u6q1v2u3k1e1q1v4x1z5x1h2e2g1f1u1x1t1v1t1q1e2t1v1u1q1k1d1x1v4x1z5x1h2i2g1f1x2t1v1t1q1e1x1t1v1u1q1p1d1x2v1x2z6x1h4g1f1x2t1v1t1q1e1x1t1v1u1q1p1d1x1z1x1z8x1g2h1g1f2x2q1t1q2e1x1t2q2p1d1x1z11x2f2x2z1x1q4e1x1t1q3p1d1x1z13x2z3x1q4e1x1t1q3p1d1x1z18x1p3k1e1x1q1p3e1d1x1z18x1d4c2d5c1x1z17x1d5c1d6c1x1z17x1d5c1d6c1x1z18x1c1d3c1x1c1d3c2x1z19x5z1x6z9"},{"n":"พ่อมด","cu":"4a1ea05922c75922c75f24d36024d44d3644612ecf6226d96c2ee86856e1732efc732efc732efc6d71fd8f5824b67b5ea671b9f3c283dec3b27b32fb843af8b38debf8f7f91b1b2f|32x48|z13x7z24x1t1k3t2u1x2z21x1u1k9x1z20x1t1k3t1u1k4t1x1z18x1t1k3u1r2q1k4x1z17x1u1k4q1r3k4t1x1z16x1k5u1r2q1k5t1x1z14x1k7t2k7x1z10x4t1k17x3z6x1g1b2d1e18d1b2x1z5x1b25x1z4x1n1g1b24x1z4x1n4v1q2s5q10x4z5x1n4w1s1r2s4r8p2x1z9x1v2w2r4s1f1r5p1f1r2p2x1z9x1o2w2r4f2r5f2p1r1p2r1x1z8x1o2w2r4p2r5p1o1r2p3x1z8x1o2w2s1r4s6r4p2x1z9x1o2w2s1r2s1w6s4p3x1z9x1o2w3r1w4s1o4w1s3p2x1z9x1o2w15s3x1z10x1o2w16s2x1z10x1o2w16s3x1z9x1o2w16s3x2z8x1o2v3w12s3u1t1i1x1z7x1o2u2t1v1w11s2v1u1t2i1x1z6x1o2u2t1k1v1w9s2q1i1u2t1i1x1z6x1o2u2t1k2u1v1w5s2v1j1b1i1u2t1i1x1z6x1o2u2t1k2t1u4j2u1t1k1d1b1i1u2t1i1x1z6x1o2u2t1k12d1b1i1u1t2i1x1z6x1o2u1t2k12d1b1i1t3i1x1z6x1o2u1t2k12d1b1i1t3i1x1z6x1o2u1t2k12d1b1i1t3i1x1z6x1o2q1s2q1k11d1b1g1q1s1q1j1x1z6x1o2r1s1g2h11d2g2q1r1s1x1z6x1o2r1q1e17g1r2x1z6x1o2s1q1e18s1x1z7x1o2w1g1e18x1z8x1o2v1e19h1x1z7x1o2q1e19h1x1z7x1o2g1e20x1z7x1o2g1e20h1x1z6x1o2g1e20h1x1z6x1o2g1e20h1x1z6x1o2g4d13g5x1z6x1o2x4f13x5z7x1o2x1z3x1f5x2f4x1z13x2z5x5z2x4z10"},{"n":"แพนด้า","cu":"161926181d2a191d2a1c212e1f2533242a373d414c4b4e595b5e68696b74787a8280828996979eadafb4babbbfcccdd0e0e1e3efeff0fdfdfdffffffffffffffffffffffff1b1b2f|32x48|z8x4z27x1f1e3x1z25x1f1b4e1x5z20x1c1b3h1k1p1t4x2z17x1d1b3k1s1t8x1z17x1b2h1r1t10x1z16x1e1g1p1t12x1z16x1o1t14x1z15x1t15x1z14x1t17x1z13x1t3r1n2q1t7r1n2x1z13x1t2q1h1b2f1o1t5q1h1b2d1x1z12x1t2j1b1i1k1e1g1r1t4j1b1i1k1e1d1x1z10x1t2q1e2q1t1i1b1n1t3q1e2q1t1i1b1x1z10x1t2q1d1b1j1l1f1b1n1t3q1d1b1j1l1f1b1x1z11x1t1s1h1b4e1q1t3s1h1b4d1x1z11x1t2o1f1b2c1m1t1r1o1q1t1o1f1b2c1f1x1z11x1t3p1k1j1n1s1t1j1b1g1r1t1p1k1j1x2z12x1t9n1i1m1s1t4x1z14x1t15x1z15x1t7s1m1k2q1t3x1z16x1t13x1z18x1t11x1z17x4t9x1z17x1e1b2l1t5s1t1x4z15x1d1e1c1b1k1t11x1z14x1d1e1c1b1k1t11x1z14x1d1e1c1b1k1t11x1z14x1d1e1c1b1k1t11x1z14x1b1c1b2k1t11x1z14x1b4k1t11x1z14x1b4k1t11x1z14x1b4k1t11x1z14x1b4k1t11x1z14x1e1b3k1t11x1z14x1f1b3h1p1j1i3j1q1m1i3a1x1z14x1d1b1d1e1x1d1e1c1b1a1x1f1e1d1b1a1c1x1z14x5d1e1c1b1a1x1f1e1d1b1a1c1x1z18x1d1e1c1b1a1x1f1e1d1b1a1c1x1z18x1c2b2a1x1e1c1b2a1c1x1z18x1b4a1x1e1b3a1c1x1z18x1b4a1x1e1b3a1c1x1z18x1b4a1x1e1b3a1c1x1z17x1f1d2b2a1f1d2c1b1a2x1z17x1c1d2b2a1f1c1d1c1b2a1x1z17x1d1b4a1f1b5a1x1z18x1d5x1d4c1d1x1z19x5z1x6z8"},{"n":"นักเดินป่า","cu":"2a29252b3a263a392f5a36252f55213b76244c812b77533155a02d3e413e4b50478257445da43f7e9d4372c949867a609c9d9877d04ed17b57ea986ffaa880cdc4bdfcfcfb1b1b2f|32x48|z12x9z21x2k1c1j6k1x2z18x1j2g1i3o5k1j1x1z16x1k1e1i3o1r6o1g1k1x1z15x1k1i3o1r8o1k1x1z14x1k1i3o1r4m5o1j1k1x3z11x1b1i3o1r2f1e3f4b4k1x1z10x1b1g1i2m2e1i4g7i1f1k1x1z9x1b1e3a1b1g4e1a6e2f1b1x1z9x1j1a5l9h1a1b3x1z10x1j1a4d1s1h3s3l1h2c1x3z7x5k1d4s2l1h1d1s1t2h3c1x1z8x1k1b4a1l1s1d2t1u1w1q1d1t1u1t1d1q1v1d1x1z7x1p1f1i2m2f1s2h2u2w1q1d1t1u1t1d1q1v1d1x1z6x1p1g1i4m1g1l1s3u4s1u1t2s1t2d1x1z6x1j1i3m1g1i2d1h1s2u5t1s2u2s1d1x1z6x1c1g1i2m1g1i1g1e1a1s2t1u4s3u2s1d1x1z6x1j1g1i3f2e2a1h1l1t1u8s1p1k1x1z6x1j1g1i2g1e3b3e1l1s1t3s3l1a1c1x1z2x3z2x1k1e1f5e1a1b1e1f1e1s7c1b1c1x1z1x1k1d1k1x1z2x1c1b1e1f1g1f1p1v1q1k1e1g1j1v1s4v1k1g1a1p1x2c1d1k1x1z2x1j1f1g1i1f1k1w3v1b1g1f1j1w1v3w1k1m1k1v1k1x1a1d1j1x1z2x1j1i3d1v1w3q1b1g2j1w5k1i1k1v1l1p1h1d1l1x1z2x1k1i1o1e1s2t1v2c1k1m1g1j1w5k1g1j1v1s5d1x1z1x1j1g1i1d1t1u1s1l2s1u2t1h1w5k1f1c1u1t1s1h1s2d1x1z1x1k1f1e1c1s1u7t1h1w5k1f1c1t2s1a1l1s1d1x2j1g1i1f1c1s1u7t1d1w5n1g1a1l1s1l1a1l1s1k1x2j1e4d1s1t6s1p1w5v1g1c1x1d2a1d1j1x1z1x1j1f1g1f1e2d1h6q1w7g1b1x3c1d1j1x1z1x1j1f3e1f1e3b2k1q1w8q1c1x1z1x1c1d1j1x1z1x1j1e1f1e2f1e3j1k1q1w9v1j1x1z1x1c1a1j1x1z1x1k1b1e3f1e2b1q4v8q1j1x1z1x1c1d1j1x1z2x1k1b1e2f2e1a1b4e7b2a1x1z1x1j1h1j1x1z3x1k1c1e4b1f1g1m1i1m1o4m3i1b1x1z1x1j1h1j1x1z4x2c1b3a1g2m1o1r3o3r2o1c1x1z1x1j1h1j1x1z6x4j1g1i1o1r3m1g1i2o1r1o1j1x1z1x1c1h1j1x1z9x1j1g1i1r4m1e1i1o1r2o1c1x1z1x1j1h1j1x1z9x1c1f1i1o4m1e1m1o3m1c1x1z1x1j1h1j1x1z9x1k1a1b1c3a1j1a1b1c3b1k1x1z1x1c1h1j1x1z10x1k1s2t2h1x1c1s1t3k1x1z2x1j1h1j1x1z10x1j1s2t2l1x1a1l1s1t2j1x1z2x1j1h1j1x1z10x1c1a1c1j2c1x1a2c1j2a1x1z2x1j1h1j1x1z10x1c2j1k1j1c1x1a2c1j2a1x1z2x1c1h1j1x1z10x1c2j2c2x1a2c3j1x1z2x1c1h1j1x1z10x1c1a1c1j3k1c1a2c1j3x1z1x1j1c1j1x1z10x1a4c1a1j1c1a3c3x1z2x1c1x1z11x1j1a2c3x2c5j1x1z2x1p1x1z12x6z2x6z4x1z3"}];
var CUI=99,SPC={},CUC={},AVC={},AVT={},CHS="abcdefghijklmnopqrstuvwx";
function cuDecode(str){
  if(typeof str!=="string"||str.length>3000)return null;if(CUC[str]!==undefined)return CUC[str];
  var r=null,m=/^((?:[0-9a-f]{6}){1,24})\|(\d{1,2})x(\d{1,2})\|((?:[a-xz]\d{1,4})+)$/.exec(str);
  if(m){var pal=m[1].match(/.{6}/g),W=+m[2],H=+m[3];
    if(W>=4&&H>=4&&W<=48&&H<=64){var cv=document.createElement("canvas");cv.width=W;cv.height=H;var g=cv.getContext("2d"),pos=0,ok=true,re=/([a-xz])(\d{1,4})/g,t;
      while((t=re.exec(m[4]))){var n=+t[2];if(t[1]!=="z"){var k=CHS.indexOf(t[1]);if(k>=pal.length){ok=false;break}g.fillStyle="#"+pal[k];
          for(var q=0;q<n;q++){var p=pos+q;g.fillRect(p%W,Math.floor(p/W),1,1)}}pos+=n;if(pos>W*H){ok=false;break}}
      if(ok&&pos===W*H)r=cv}}
  var ks=Object.keys(CUC);if(ks.length>60)delete CUC[ks[0]];CUC[str]=r;return r}
function cuHash(str){var h=5381;for(var i=0;i<str.length;i++)h=((h*33)^str.charCodeAt(i))>>>0;return h.toString(36)}
function isCustom(){return (S.gAv|0)===CUI&&!!S.gCu&&!!cuDecode(S.gCu)}
function myAv(){if(isCustom())return cuDecode(S.gCu);var a=S.gAv|0;if(a===CUI)a=0;return clamp(a,0,SPR.length-1)}
function avFallback(id){var h=0;for(var i=0;i<id.length;i++)h=(h*31+id.charCodeAt(i))>>>0;return h%SPR.length}
function avIdx(v,id){var a=Math.round(+v);return (isFinite(a)&&a>=0&&a<SPR.length)?a:avFallback(id)}
var BLANK=null;
function spriteImg(i){if(i&&i.nodeType)return i;var d=SPR[clamp(i|0,0,SPR.length-1)],im=d&&d.cu?cuDecode(d.cu):null;
  if(im)return im;if(!BLANK){BLANK=document.createElement("canvas");BLANK.width=BLANK.height=16}return BLANK}
function spriteDim(im,px){var D=px*(im.height>im.width?1.35:1);return im.height>im.width?{w:D*im.width/im.height,h:D}:{w:D,h:D*im.height/im.width}}
function drawSprite(c,i,cx,by,px){var im=spriteImg(i),d=spriteDim(im,px);c.save();c.imageSmoothingEnabled=false;c.drawImage(im,Math.round(cx-d.w/2),Math.round(by-d.h),Math.round(d.w),Math.round(d.h));c.restore()}
function spriteCanvas(i,px){var im=spriteImg(i),cv=document.createElement("canvas"),k=px/Math.max(im.width,im.height);cv.width=im.width;cv.height=im.height;
  cv.style.width=Math.round(im.width*k)+"px";cv.style.height=Math.round(im.height*k)+"px";cv.style.imageRendering="pixelated";
  cv.getContext("2d").drawImage(im,0,0);return cv}
function marker8(c,x,y,av,color,name,stale){
  c.save();c.globalAlpha=stale?.55:1;
  c.beginPath();c.ellipse(x,y,10,4.5,0,0,6.283);c.fillStyle=color;c.fill();c.lineWidth=2;c.strokeStyle=css("--surface");c.stroke();
  if(stale){c.setLineDash([3,3]);c.lineWidth=1.5;c.strokeStyle=color;c.beginPath();c.ellipse(x,y,15,7,0,0,6.283);c.stroke();c.setLineDash([])}
  drawSprite(c,av,x,y+3,38);
  if(name){c.font="600 11px "+css("--font");c.textAlign="center";c.textBaseline="alphabetic";c.lineWidth=3;c.strokeStyle=css("--surface");c.strokeText(name,x,y+19);c.fillStyle=css("--ink");c.fillText(name,x,y+19)}
  c.restore()}
function friendMarker(c,x,y,f){marker8(c,x,y,f.av,f.color,f.name,f.stale)}
function ownMarker(c,x,y){marker8(c,x,y,myAv(),(grp.on&&!S.gView&&grp.myColor)?grp.myColor:css("--gps"),(grp.on&&grp.name&&!S.gView)?grp.name:"",false)}
function spriteAt(c,i,x,yPt,sz){var d=spriteDim(spriteImg(i),sz),by=Math.max(yPt-4,d.h+2);drawSprite(c,i,x,by,sz)}

async function gPush(){
  if(S.gView||!S.gShare||!gpsFix)return;
  var now=Date.now();
  if(now-grp.lastTry<8000&&gpsFix.t===grp.lastFix)return;
  if(gpsFix.t===grp.lastFix&&now-grp.lastTry<30000)return;
  grp.lastTry=now;
  var body=JSON.stringify({n:grp.name,la:Math.round(gpsFix.lat*1e6)/1e6,lo:Math.round(gpsFix.lon*1e6)/1e6,ac:Math.round(gpsFix.acc),t:gpsFix.t,k:(route&&!route.sample&&gpsKm!=null?Math.round(gpsKm*100)/100:null),av:(isCustom()?CUI:myAv()),ch:(isCustom()?cuHash(S.gCu):null),s:{".sv":"timestamp"}});
  try{
    var t0=Date.now(),r=await fetchT(fbBase()+"/rooms/"+grp.room+"/"+myUid()+".json",{method:"PUT",body:body,headers:{"Content-Type":"application/json"}},8000);
    if(!r.ok)throw new Error("HTTP "+r.status);
    grp.sentLocal=(t0+Date.now())/2;grp.lastOk=Date.now();grp.lastFix=gpsFix.t;grp.pushErr="";
  }catch(e){grp.pushErr=(e&&/HTTP (401|403)/.test(e.message))?"ฐานข้อมูลไม่อนุญาต ตรวจกฎ (rules)":"ส่งตำแหน่งไม่ได้ (ไม่มีสัญญาณ)"}
}
async function gSyncAv(){
  if(S.gView||!isCustom())return;var key=grp.room+"|"+cuHash(S.gCu);if(grp.avKey===key)return;
  var r=await fetchT(fbBase()+"/avatars/"+grp.room+"/"+myUid()+".json",{method:"PUT",body:JSON.stringify(S.gCu),headers:{"Content-Type":"application/json"}},10000);
  if(!r.ok)throw new Error("HTTP "+r.status);grp.avKey=key}
function gDelMine(room){try{fetchT(fbBase()+"/rooms/"+room+"/"+myUid()+".json",{method:"DELETE"},5000);fetchT(fbBase()+"/avatars/"+room+"/"+myUid()+".json",{method:"DELETE"},5000)}catch(e){}}
async function gPoll(){
  try{
    var r=await fetchT(fbBase()+"/rooms/"+grp.room+".json",{cache:"no-store"},8000);
    if(!r.ok)throw new Error("HTTP "+r.status);
    var data=await r.json(),me=null,list=[],mine=myUid();
    if(data&&typeof data==="object"){
      Object.keys(data).forEach(function(k){
        if(k==="_route")return;var d=data[k];if(!d||typeof d!=="object")return;
        var la=+d.la,lo=+d.lo,s=+d.s;if(!isFinite(la)||!isFinite(lo)||!isFinite(s)||Math.abs(la)>90||Math.abs(lo)>180)return;
        if(k===mine){me=d;return}
        list.push({id:k,av:(+d.av===CUI?CUI:avIdx(d.av,k)),ch:String(d.ch||"").slice(0,12),k:(d.k==null?null:+d.k),name:String(d.n||"?").slice(0,24),lat:la,lon:lo,acc:+d.ac||0,t:+d.t||s,s:s,color:colorOf(k)});
      });
    }
    if(me&&isFinite(+me.s)&&grp.sentLocal)grp.offset=+me.s-grp.sentLocal;
    var now=Date.now()+grp.offset;
    list.forEach(function(f){
      f.u=(f.lon+180)/360;f.v=merc(f.lat);f.age=Math.max(0,now-f.s);f.stale=f.age>5*60000;
      f.km=null;f.off=null;f.ni=0;
      if(route&&!route.sample){var q=nearestIn(f.lat,f.lon,0,route.n);f.km=q.km;f.off=q.off;f.ni=q.i}
      else if(isFinite(f.k)&&f.k!=null){f.km=f.k;f.ni=route?clamp(Math.round(f.k*1000/route.step),0,route.n):0}
    });
    list=list.filter(function(f){return f.age<12*3600000});
    var cmap=assignColors(list.map(function(f){return f.id}).concat([mine]));grp.myColor=cmap[mine];
    list.forEach(function(f){f.color=cmap[f.id]||f.color});
    var need=[];
    list.forEach(function(f){if(f.av!==CUI)return;var key=f.id+"|"+f.ch;if(AVC[key]){f.av=AVC[key]}else{f.av=avFallback(f.id);need.push({f:f,key:key})}});
    for(var ni=0;ni<need.length&&ni<6;ni++){var nd=need[ni];if(Date.now()-(AVT[nd.key]||0)<20000)continue;AVT[nd.key]=Date.now();
      try{var ar=await fetchT(fbBase()+"/avatars/"+grp.room+"/"+nd.f.id+".json",{cache:"no-store"},8000);
        if(ar.ok){var cs=await ar.json(),cc=cuDecode(cs);if(cc&&cuHash(cs)===nd.f.ch){AVC[nd.key]=cc;nd.f.av=cc}}}catch(e){}}
    list.forEach(function(f){var tr=grp.trails[f.id]||(grp.trails[f.id]=[]),last=tr[tr.length-1];
      if(!last||Math.abs(last[0]-f.u)+Math.abs(last[1]-f.v)>2e-8){tr.push([f.u,f.v,f.ni||0]);if(tr.length>900)tr.splice(0,200)}});
    grp.friends=list;grp.pollErr="";
  }catch(e){grp.pollErr=(e&&/HTTP (401|403)/.test(e.message))?"ฐานข้อมูลไม่อนุญาต ตรวจกฎ (rules)":"ไม่มีสัญญาณอินเทอร์เน็ต"}
}
function routeId(r){return Math.round(r.total)+"_"+r.n}
function routePack(){var st=Math.max(1,Math.round(40/route.step)),out=[],pl=0,po=0,pe=0,i,idx=[];
  for(i=0;i<route.n;i+=st)idx.push(i);idx.push(route.n);
  idx.forEach(function(i){var la=Math.round(route.lat[i]*1e5),lo=Math.round(route.lon[i]*1e5),el=Math.round(route.ele[i]);out.push((la-pl)+","+(lo-po)+","+(el-pe));pl=la;po=lo;pe=el});
  return out.join(";")}
function routeUnpack(p){var pts=[],la=0,lo=0,el=0;
  String(p).split(";").forEach(function(t){var q=t.split(",");la+=+q[0];lo+=+q[1];el+=+q[2];
    if(!isFinite(la)||!isFinite(lo)||!isFinite(el)||Math.abs(la)>9e6||Math.abs(lo)>18e6)throw new Error("bad route");pts.push([la/1e5,lo/1e5,el])});
  if(pts.length<2)throw new Error("bad route");return pts}
function restoreOwn(){
  if(ownPlan){cps=ownPlan.cps;planStart=ownPlan.ps;ownPlan=null;renderCps();$("planStart").value=planStart;save()}
  if(route&&route.viewer){var r=LS.get("tcc.route"),nr=null;if(r){try{nr=build(JSON.parse(r))}catch(e){}}setRoute(nr||sampleRoute(),false)}
}
async function gSyncRoute(){
  var base=fbBase()+"/routes/"+grp.room,real=route&&!route.sample&&!route.viewer;
  if(real&&!S.gView){
    var id=routeId(route),key=grp.room+"|"+id;if(grp.routeKey===key)return;
    var r=await fetchT(base+"/h.json",{cache:"no-store"},8000);if(!r.ok)throw new Error("HTTP "+r.status);
    var hh=await r.json();
    if(hh!==id){
      var body=JSON.stringify({nm:String(route.name||"").slice(0,40),h:id,tot:Math.round(route.total),p:routePack(),
        c:JSON.stringify(cps.map(function(x){return [String(x.name||"").slice(0,20),x.km,x.time]})),ps:planStart,s:{".sv":"timestamp"}});
      var r2=await fetchT(base+".json",{method:"PUT",body:body,headers:{"Content-Type":"application/json"}},15000);
      if(!r2.ok)throw new Error("HTTP "+r2.status);
    }
    grp.routeKey=key;return;
  }
  if(real)return;
  var now=Date.now();if(now-grp.routeTried<(route&&route.viewer?60000:15000))return;grp.routeTried=now;
  var q=await fetchT(base+".json",{cache:"no-store"},15000);if(!q.ok)throw new Error("HTTP "+q.status);
  var d=await q.json();if(!d||!d.p)return;
  if(route&&route.viewer&&route.vh===d.h)return;
  var R=build({name:String(d.nm||"เส้นทางจากกลุ่ม"),pts:routeUnpack(d.p)});R.viewer=true;R.vh=d.h;
  if(S.gView&&d.c){try{var cc=JSON.parse(d.c).map(function(x){return {name:String(x[0]),km:+x[1],time:String(x[2])}}).filter(function(x){return isFinite(x.km)&&/^\d{1,2}:\d{2}$/.test(x.time)});
    if(cc.length){if(!ownPlan)ownPlan={cps:cps,ps:planStart};cps=cc;if(/^\d{1,2}:\d{2}$/.test(d.ps||""))planStart=d.ps;renderCps();$("planStart").value=planStart}}catch(e){}}
  setRoute(R,false);$("gpxMsg").className="msg";$("gpxMsg").textContent="ใช้เส้นทางจากกลุ่ม "+grp.room+" (ดูอย่างเดียว ไม่ได้บันทึกในเครื่อง)";
}
async function gCycle(){
  if(!grp.on||grp.busy)return;grp.busy=true;
  try{try{await gSyncAv()}catch(e){}await gPush();try{await gSyncRoute()}catch(e){}await gPoll()}finally{grp.busy=false}
  renderGroup();drawAll();
}
function gLoop(){clearTimeout(grp.timer);if(!grp.on)return;gCycle().then(function(){grp.timer=setTimeout(gLoop,5000)})}

function gStatus(){
  var m=$("gMsg");
  if(!fbBase()){m.className="msg err";m.textContent="ยังไม่ได้ตั้งค่าฐานข้อมูล Firebase (ดูหัวข้อ ตั้งค่า Firebase ด้านล่าง)";return}
  if(!grp.on){m.className="msg";m.textContent="ยังไม่ได้เข้ากลุ่ม";return}
  var err=grp.pushErr||grp.pollErr;
  if(err){m.className="msg err";m.textContent=err+(grp.lastOk?" · ส่งสำเร็จล่าสุด "+hhmm(grp.lastOk)+" น.":"");return}
  m.className="msg";
  if(S.gView){m.textContent="โหมดผู้ชม · เชื่อมต่อแล้ว (ไม่ส่งตำแหน่งของคุณ)";return}
  m.textContent="เชื่อมต่อแล้ว · "+(S.gShare?(gpsFix?"ส่งตำแหน่งล่าสุด "+hhmm(grp.lastOk||Date.now())+" น.":"เปิด GPS ที่แท็บตั้งค่าเพื่อแชร์ตำแหน่ง"):"หยุดแชร์ตำแหน่งของคุณอยู่ (ยังเห็นเพื่อน)");
}
function renderGroup(){
  gStatus();
  var box=$("gList");box.textContent="";
  $("gLeave").hidden=!grp.on;$("gJoin").textContent=grp.on?"อัปเดตชื่อ/รหัส":"เข้าร่วมกลุ่ม";
  var line=$("grpLine");
  if(!grp.on){line.hidden=true;return}
  var viewer=!!S.gView,rt=route&&!route.sample?route.total/1000:null,myKm=runnerKm(),rows=(viewer?[]:[{me:true,av:myAv(),name:grp.name||"ฉัน",km:myKm,color:grp.myColor||"#e8590c",off:offRoute?(gpsFix?gpsFix.off:0):null,age:0,stale:false}]).concat(grp.friends.map(function(f){return f}));
  rows.sort(function(a,b){return (b.km==null?-1:b.km)-(a.km==null?-1:a.km)});
  var head=document.createElement("div");head.className="ghead";["ชื่อ","กม.",viewer?"เหลือ":"ต่างจากฉัน","เห็นเมื่อ"].forEach(function(t){var s=document.createElement("span");s.textContent=t;head.appendChild(s)});box.appendChild(head);
  rows.forEach(function(f){
    var r=document.createElement("div");r.className="grow"+(f.me?" me":"");
    var nm=document.createElement("span");nm.className="gn";
    var dot=document.createElement("i");dot.className="gdot";dot.style.background=f.color;dot.appendChild(spriteCanvas(f.av==null?myAv():f.av,24));
    var tx=document.createElement("span");var t1=document.createElement("b");t1.textContent=f.name+(f.me?" (ฉัน)":"");
    var t2=document.createElement("small");
    var offLim=Math.max(S.offDist||50,f.acc||0);
    if(f.me)t2.textContent=f.off!=null?"ออกนอกเส้นทาง "+Math.round(f.off)+" ม.":(gpsFix?"บนเส้นทาง":"ยังไม่เปิด GPS");
    else if(f.off!=null&&f.off>offLim){t2.textContent="ออกนอกเส้นทาง "+Math.round(f.off)+" ม.";t2.className="bad"}
    else t2.textContent=f.km!=null?"บนเส้นทาง":"ไม่มีเส้นทาง";
    if(!f.me&&f.stale){t2.textContent+=" · สัญญาณเก่า";t2.className="bad"}
    tx.appendChild(t1);tx.appendChild(document.createElement("br"));tx.appendChild(t2);nm.appendChild(dot);nm.appendChild(tx);r.appendChild(nm);
    var c2=document.createElement("span");c2.className="n mono";c2.textContent=f.km!=null?f.km.toFixed(1):"-";r.appendChild(c2);
    var c3=document.createElement("span");c3.className="n mono";c3.textContent=viewer?(f.km!=null&&rt!=null?Math.max(0,rt-f.km).toFixed(1)+" กม.":"-"):f.me?"-":(f.km!=null?(f.km-myKm>=0?"+":"−")+Math.abs(f.km-myKm).toFixed(1)+" กม.":"-");r.appendChild(c3);
    var c4=document.createElement("span");c4.className="n mono"+(f.stale?" bad":"");c4.textContent=f.me?"ตอนนี้":ageTxt(f.age)+"ก่อน";r.appendChild(c4);
    box.appendChild(r);
  });
  if(!grp.friends.length){var em=document.createElement("div");em.className="hempty";em.textContent=(viewer?"ยังไม่มีเพื่อนส่งตำแหน่งในกลุ่มนี้":"ยังไม่มีเพื่อนในกลุ่ม ส่งลิงก์เชิญให้เพื่อนเปิดแล้วกดเข้าร่วม");box.appendChild(em)}
  // สรุปบนหน้าหลัก
  var ahead=null,behind=null;
  grp.friends.forEach(function(f){if(f.km==null)return;var d=f.km-myKm;if(d>=0&&(!ahead||d<ahead.d))ahead={d:d,f:f};if(d<0&&(!behind||-d<behind.d))behind={d:-d,f:f}});
  var txt=viewer?"ผู้ชม · กลุ่ม "+grp.room+" · "+grp.friends.length+" คนกำลังวิ่ง":"กลุ่ม "+grp.room+" · "+(grp.friends.length+1)+" คน";
  if(viewer){var lead=null;grp.friends.forEach(function(f){if(f.km!=null&&(!lead||f.km>lead.km))lead=f});if(lead)txt+=" · นำ: "+lead.name+" กม. "+lead.km.toFixed(1)}
  if(!viewer&&ahead)txt+=" · นำหน้า: "+ahead.f.name+" +"+ahead.d.toFixed(1)+" กม.";
  if(!viewer&&behind)txt+=" · ตามหลัง: "+behind.f.name+" −"+behind.d.toFixed(1)+" กม.";
  line.hidden=false;line.textContent=txt;
}
function joinGroup(){
  var name=$("gName").value.trim().slice(0,24),room=$("gRoom").value.trim().toUpperCase().replace(/[^A-Z0-9]/g,""),m=$("gMsg");
  if(!name&&S.gView)name="ผู้ชม";
  if(!name){m.className="msg err";m.textContent="ใส่ชื่อของคุณก่อน (หรือเลือกโหมดผู้ชม)";return}
  if(!roomOk(room)){m.className="msg err";m.textContent="รหัสกลุ่มต้องเป็นตัวอักษร A-Z หรือเลข 4-12 ตัว";return}
  if(!fbBase()){gStatus();return}
  var changed=grp.on&&(grp.room!==room);
  if(changed){gDelMine(grp.room)}
  grp.on=true;grp.room=room;grp.name=name;grp.friends=[];grp.trails={};grp.lastFix=0;grp.lastTry=0;grp.routeKey="";grp.routeTried=0;grp.avKey="";grp.avKey="";
  S.gName=S.gView&&name==="ผู้ชม"?(S.gName||""):name;S.gRoom=room;S.gOn=true;save();$("gRoom").value=room;unlockAudio();
  gLoop();renderGroup();
}
function leaveGroup(){
  if(!grp.on)return;
  gDelMine(grp.room)
  grp.on=false;grp.friends=[];grp.trails={};clearTimeout(grp.timer);S.gOn=false;save();restoreOwn();renderGroup();drawAll();
}
$("gJoin").onclick=joinGroup;$("gLeave").onclick=leaveGroup;
$("gNew").onclick=function(){var a="ABCDEFGHJKLMNPQRSTUVWXYZ23456789",s="";for(var i=0;i<6;i++)s+=a.charAt(Math.floor(Math.random()*a.length));$("gRoom").value=s};
$("gView").onchange=function(e){S.gView=e.target.checked;save();
  if(grp.on){if(S.gView){gDelMine(grp.room)}else restoreOwn();grp.routeKey="";grp.routeTried=0;gLoop()}
  renderGroup();drawAll()};
$("gCopyV").onclick=function(){var room=($("gRoom").value||grp.room||"").trim().toUpperCase().replace(/[^A-Z0-9]/g,"");
  if(!roomOk(room)){$("gMsg").className="msg err";$("gMsg").textContent="สร้างหรือใส่รหัสกลุ่มก่อน";return}
  copyText(location.href.split("#")[0]+"#g="+room+"&v=1",$("gCopyV"),"คัดลอกลิงก์ผู้ชม")};
function pickAv(i){S.gAv=i;save();buildPicker();grp.lastFix=0;grp.lastTry=0;if(grp.on)gCycle();renderGroup();drawAll()}
/* รูปถ่าย -> พิกเซล 16x16 (ประมวลผลในเครื่อง ไม่อัปโหลดรูปจริง) */
function medianCut(cols,K){
  var boxes=[cols.slice()];
  while(boxes.length<K){
    var bi=-1,bs=0,ch=0;
    boxes.forEach(function(b,i){if(b.length<2)return;for(var k=0;k<3;k++){var lo=255,hi=0;b.forEach(function(p){if(p[k]<lo)lo=p[k];if(p[k]>hi)hi=p[k]});var sp=(hi-lo)*Math.sqrt(b.length);if(sp>bs){bs=sp;bi=i;ch=k}}});
    if(bi<0)break;var b=boxes[bi];b.sort(function(a,c){return a[ch]-c[ch]});var mid=b.length>>1;boxes.splice(bi,1,b.slice(0,mid),b.slice(mid));
  }
  return boxes.filter(function(b){return b.length}).map(function(b){var r=0,g=0,bl=0;b.forEach(function(p){r+=p[0];g+=p[1];bl+=p[2]});return [Math.round(r/b.length),Math.round(g/b.length),Math.round(bl/b.length)]});
}
function photoToCu(img,rmBg,K){K=K||23;
  var W=32,H=48,WW=192,WH=288,wc=document.createElement("canvas");wc.width=WW;wc.height=WH;var g=wc.getContext("2d");g.imageSmoothingQuality="high";
  g.fillStyle="#fff";g.fillRect(0,0,WW,WH);
  var sc,dw,dh;
  if(rmBg){sc=Math.min(WW/img.width,WH/img.height);dw=img.width*sc;dh=img.height*sc;g.drawImage(img,(WW-dw)/2,(WH-dh)/2,dw,dh)}
  else{sc=Math.max(WW/img.width,WH/img.height);dw=img.width*sc;dh=img.height*sc;g.drawImage(img,(WW-dw)/2,(WH-dh)*0.2,dw,dh)}
  var d=g.getImageData(0,0,WW,WH).data,n=WW*WH,px=new Array(n),i,x,y,k;
  for(i=0;i<n;i++){var r=d[i*4],gg=d[i*4+1],b=d[i*4+2],m=(r+gg+b)/3;
    r=clamp(m+(r-m)*1.25,0,255);gg=clamp(m+(gg-m)*1.25,0,255);b=clamp(m+(b-m)*1.25,0,255);
    r=clamp((r-128)*1.1+128,0,255);gg=clamp((gg-128)*1.1+128,0,255);b=clamp((b-128)*1.1+128,0,255);px[i]=[r,gg,b]}
  var dist=function(a,b){return Math.sqrt((a[0]-b[0])*(a[0]-b[0])+(a[1]-b[1])*(a[1]-b[1])+(a[2]-b[2])*(a[2]-b[2]))};
  var op=new Uint8Array(n);
  if(rmBg){
    var bg=[0,0,0],cs=[0,WW-1,WW*(WH-1),n-1];cs.forEach(function(c){bg[0]+=d[c*4]/4;bg[1]+=d[c*4+1]/4;bg[2]+=d[c*4+2]/4});
    var raw=function(c){return [d[c*4],d[c*4+1],d[c*4+2]]};
    for(i=0;i<n;i++)op[i]=1;var q=[];
    for(i=0;i<WW;i++){q.push(i,WW*(WH-1)+i)}for(i=0;i<WH;i++){q.push(i*WW,i*WW+WW-1)}
    while(q.length){k=q.pop();if(!op[k])continue;if(dist(raw(k),bg)>64)continue;op[k]=0;x=k%WW;y=(k-x)/WW;
      if(x>0)q.push(k-1);if(x<WW-1)q.push(k+1);if(y>0)q.push(k-WW);if(y<WH-1)q.push(k+WW)}
  }else{for(y=0;y<WH;y++)for(x=0;x<WW;x++){var ex=(x-(WW-1)/2)/(WW/2),ey=(y-(WH-1)/2)/(WH/2);op[y*WW+x]=ex*ex+ey*ey<=1?1:0}}
  // เก็บเฉพาะก้อนใหญ่ (ตัดข้อความ/ขอบจอ/สิ่งเล็กๆ รอบตัว)
  var lab=new Int32Array(n),sizes=[0],nl=0,stk=[];
  for(i=0;i<n;i++){if(!op[i]||lab[i])continue;nl++;lab[i]=nl;stk.push(i);var sz=0;
    while(stk.length){k=stk.pop();sz++;x=k%WW;y=(k-x)/WW;
      if(x>0&&op[k-1]&&!lab[k-1]){lab[k-1]=nl;stk.push(k-1)}if(x<WW-1&&op[k+1]&&!lab[k+1]){lab[k+1]=nl;stk.push(k+1)}
      if(y>0&&op[k-WW]&&!lab[k-WW]){lab[k-WW]=nl;stk.push(k-WW)}if(y<WH-1&&op[k+WW]&&!lab[k+WW]){lab[k+WW]=nl;stk.push(k+WW)}}
    sizes.push(sz)}
  var big=Math.max.apply(null,sizes.concat([1]));
  for(i=0;i<n;i++)if(op[i]&&sizes[lab[i]]<big*0.12)op[i]=0;
  var x0=WW,x1=-1,y0=WH,y1=-1;
  for(y=0;y<WH;y++)for(x=0;x<WW;x++)if(op[y*WW+x]){if(x<x0)x0=x;if(x>x1)x1=x;if(y<y0)y0=y;if(y>y1)y1=y}
  if(x1<0)throw new Error("empty");
  var bw=x1-x0+1,bh=y1-y0+1,s2=Math.min((W-2)/bw,(H-2)/bh),tw=Math.max(1,Math.round(bw*s2)),th=Math.max(1,Math.round(bh*s2)),
      ox=1+((W-2-tw)>>1),oy=rmBg?(H-1-th):(1+((H-2-th)>>1));
  var tp=new Array(W*H),to=new Uint8Array(W*H);
  for(var ty=0;ty<th;ty++)for(var tx=0;tx<tw;tx++){
    var sx0=x0+tx/s2,sx1=x0+(tx+1)/s2,sy0=y0+ty/s2,sy1=y0+(ty+1)/s2,r2=0,g2=0,b2=0,c2=0,tot=0;
    for(y=Math.floor(sy0);y<Math.ceil(sy1);y++)for(x=Math.floor(sx0);x<Math.ceil(sx1);x++){
      if(x<0||y<0||x>=WW||y>=WH)continue;tot++;var ix=y*WW+x;if(!op[ix])continue;c2++;r2+=px[ix][0];g2+=px[ix][1];b2+=px[ix][2]}
    if(tot&&c2/tot>=0.5){var o=(oy+ty)*W+ox+tx;to[o]=1;tp[o]=[r2/c2,g2/c2,b2/c2]}}
  // ลบจุดโดดเดี่ยว
  for(y=0;y<H;y++)for(x=0;x<W;x++){var o2=y*W+x;if(to[o2]&&!((x>0&&to[o2-1])||(x<W-1&&to[o2+1])||(y>0&&to[o2-W])||(y<H-1&&to[o2+W])))to[o2]=0}
  var cols=[];for(i=0;i<W*H;i++)if(to[i])cols.push(tp[i]);
  if(cols.length<30)throw new Error("empty");
  var pal=medianCut(cols,K).map(function(p){return [Math.round(p[0]),Math.round(p[1]),Math.round(p[2])]}),idx=new Array(W*H);
  for(i=0;i<W*H;i++){
    if(to[i]){var bi=0,bd=1e9;pal.forEach(function(p,k2){var dd=dist(p,tp[i]);if(dd<bd){bd=dd;bi=k2}});idx[i]=bi;continue}
    x=i%W;y=(i-x)/W;var nb=(x>0&&to[i-1])||(x<W-1&&to[i+1])||(y>0&&to[i-W])||(y<H-1&&to[i+W]);
    idx[i]=nb?pal.length:-1}
  var all=pal.concat([[27,27,47]]),hex=function(v){return (v<16?"0":"")+v.toString(16)},out=[],run=1,prev=idx[0];
  for(i=1;i<=W*H;i++){if(i<W*H&&idx[i]===prev){run++}else{out.push((prev<0?"z":CHS.charAt(prev))+run);prev=idx[i];run=1}}
  return all.map(function(p){return hex(p[0])+hex(p[1])+hex(p[2])}).join("")+"|"+W+"x"+H+"|"+out.join("");
}
var avImg=null;
function avProcess(){
  var m=$("avMsg");if(!avImg)return;
  try{var cu,ks=[23,16,12,8,6],ki=0;do{cu=photoToCu(avImg,$("avBg").checked,ks[ki++])}while(cu.length>2900&&ki<ks.length);if(cu.length>2900)throw new Error("big");if(!cuDecode(cu))throw new Error("bad");
    S.gCu=cu;S.gAv=CUI;save();buildPicker();grp.lastFix=0;grp.lastTry=0;if(grp.on)gCycle();renderGroup();drawAll();
    m.className="msg";m.textContent="สร้างตัวละครจากรูปแล้ว (รูปจริงไม่ถูกส่งออกจากเครื่อง ส่งเฉพาะภาพพิกเซลเล็กๆ)"}
  catch(e){m.className="msg err";m.textContent="แปลงรูปไม่สำเร็จ ลองรูปที่เห็นหน้าชัดขึ้น หรือลองติ๊ก/เอาติ๊ก ลบพื้นหลัง"}
}
$("avUp").onclick=function(){$("avFile").click()};
$("avFile").addEventListener("change",function(e){
  var f=e.target.files&&e.target.files[0];e.target.value="";if(!f)return;
  var m=$("avMsg");m.className="msg";m.textContent="กำลังแปลงรูป...";
  var url=URL.createObjectURL(f),im=new Image();
  im.onload=function(){URL.revokeObjectURL(url);avImg=im;avProcess()};
  im.onerror=function(){URL.revokeObjectURL(url);m.className="msg err";m.textContent="เปิดรูปนี้ไม่ได้ ลองรูป JPG หรือ PNG"};
  im.src=url});
$("avBg").onchange=function(){if(avImg)avProcess()};
function buildPicker(){
  var box=$("avPick");box.textContent="";
  SPR.forEach(function(d,i){var b=document.createElement("button");b.type="button";b.className="avb";b.setAttribute("aria-pressed",(S.gAv|0)===i);b.setAttribute("aria-label",d.n);
    b.appendChild(spriteCanvas(i,44));var t=document.createElement("span");t.textContent=d.n;b.appendChild(t);
    b.onclick=function(){pickAv(i)};box.appendChild(b)});
  var cc=S.gCu&&cuDecode(S.gCu);
  if(cc){var b2=document.createElement("button");b2.type="button";b2.className="avb";b2.setAttribute("aria-pressed",(S.gAv|0)===CUI);b2.setAttribute("aria-label","รูปของฉัน");
    b2.appendChild(spriteCanvas(cc,44));var t2=document.createElement("span");t2.textContent="รูปของฉัน";b2.appendChild(t2);b2.onclick=function(){pickAv(CUI)};box.appendChild(b2)}
  var pv=$("avPrev");pv.textContent="";pv.appendChild(spriteCanvas(myAv(),56));
  var n=document.createElement("b");n.textContent=$("gName").value.trim()||"ชื่อของคุณ";pv.appendChild(n)}
$("gName").addEventListener("input",function(){var b=$("avPrev").lastChild;if(b)b.textContent=$("gName").value.trim()||"ชื่อของคุณ"});
$("gShare").onchange=function(e){S.gShare=e.target.checked;save();if(grp.on)gStatus()};
$("fbUrl").addEventListener("change",function(){S.fbUrl=$("fbUrl").value.trim();save();renderGroup()});
function copyText(txt,btn,label){
  var done=function(ok){btn.textContent=ok?"คัดลอกแล้ว":"คัดลอกไม่ได้ ลองกดค้างที่ข้อความ";setTimeout(function(){btn.textContent=label},2000)};
  try{navigator.clipboard.writeText(txt).then(function(){done(true)},function(){done(false)})}catch(e){done(false)}
}
$("gCopy").onclick=function(){var room=($("gRoom").value||grp.room||"").trim().toUpperCase().replace(/[^A-Z0-9]/g,"");
  if(!roomOk(room)){$("gMsg").className="msg err";$("gMsg").textContent="สร้างหรือใส่รหัสกลุ่มก่อน";return}
  copyText(location.href.split("#")[0]+"#g="+room,$("gCopy"),"คัดลอกลิงก์เชิญ")};
$("fbRules").value=GRULES;
$("fbCopy").onclick=function(){copyText(GRULES,$("fbCopy"),"คัดลอกกฎ (rules)")};
setInterval(function(){if(grp.on&&!$("p-grp").hidden)renderGroup()},1000);

/* ================= tabs ================= */
var tabs=["map","hill","cut","grp","set"];
function showTab(t){tabs.forEach(function(k){var on=k===t;$("t-"+k).setAttribute("aria-selected",on);$("p-"+k).hidden=!on});
  if(t==="hill"){renderHills();drawCharts()}if(t==="map"){drawAll()}if(t==="set"){countHave()}if(t==="grp"){renderGroup()}}
tabs.forEach(function(k){$("t-"+k).onclick=function(){showTab(k)}});

/* ================= install + service worker ================= */
var deferred=null;
window.addEventListener("beforeinstallprompt",function(e){e.preventDefault();deferred=e;$("installBtn").hidden=false});
$("installBtn").onclick=function(){if(!deferred)return;deferred.prompt();deferred.userChoice.finally(function(){deferred=null;$("installBtn").hidden=true})};
function regSW(){
  var m=$("swMsg");
  if(!("serviceWorker" in navigator)){m.textContent="เบราว์เซอร์นี้ไม่รองรับการใช้ออฟไลน์";return}
  navigator.serviceWorker.register("sw.js").then(function(r){swReg=r;
    navigator.serviceWorker.ready.then(function(){m.className="msg";m.textContent="พร้อมใช้ออฟไลน์แล้ว"})
  }).catch(function(){m.className="msg";m.textContent="หน้านี้ยังไม่ได้เปิดผ่านโฮสต์ของตัวเอง จึงยังใช้ออฟไลน์ไม่ได้ (ตัวแอปยังทำงานปกติเมื่อมีเน็ต)"});
}

/* ================= boot ================= */
load();
$("planStart").value=planStart;
$("simKm").value=simKm;$("simKmV").textContent=simKm.toFixed(1);
$("shift").value=shiftH;$("shiftV").textContent=shiftH.toFixed(1);
$("aOn").checked=S.alertOn;$("aVib").checked=S.vib;$("aSnd").checked=S.snd;$("aLead").value=S.lead;$("aGain").value=S.minGain;$("aSteep").value=S.steep;$("aOff").checked=S.offOn;$("aOffD").value=S.offDist;
$("tUrl").value=S.tileUrl||"";$("tAttr").value=S.tileAttr||"";$("sUrl").value=S.satUrl||"";$("sAttr").value=S.satAttr||"";$("dUrl").value=S.demUrl||"";
if(S.exv!==2){S.ex=1;S.exv=2;save()}
G.exI=Math.max(0,EXS.indexOf(S.ex));$("r3E").textContent="สูง×"+EXS[G.exI];$("mRoad").setAttribute("aria-pressed",S.base!=="sat");$("mSat").setAttribute("aria-pressed",S.base==="sat");
loadTrail();renderCps();renderLegend();filterBtns();
if(!route){route=sampleRoute();$("gpxMsg").textContent="กำลังแสดงเส้นทางตัวอย่าง อัปโหลด GPX จริงได้ที่นี่"}
else{$("gpxMsg").textContent=(route.name?route.name+" · ":"")+(route.total/1000).toFixed(1)+" กม. โหลดจากที่บันทึกไว้ในเครื่อง"}
var _r=route;route=null;setRoute(_r,false);
lastKm=runnerKm();
window.addEventListener("resize",function(){drawAll()});
try{window.matchMedia("(prefers-color-scheme: dark)").addEventListener("change",function(){drawAll()})}catch(e){}
$("gName").value=S.gName||"";$("gRoom").value=S.gRoom||"";if(S.gCu&&!cuDecode(S.gCu)){S.gCu="";if((S.gAv|0)===8||(S.gAv|0)===CUI)S.gAv=0}else if(S.gCu&&(S.gAv|0)===8)S.gAv=CUI;
buildPicker();$("gShare").checked=S.gShare!==false;$("gView").checked=!!S.gView;$("fbUrl").value=S.fbUrl||"";
var hm=/[#&]g=([A-Za-z0-9]{4,12})/.exec(location.hash);
if(hm){$("gRoom").value=hm[1].toUpperCase();showTab("grp");$("gMsg").className="msg";
  if(/[#&]v=1/.test(location.hash)){S.gView=true;$("gView").checked=true;save();if(fbBase())joinGroup();else gStatus()}
  else $("gMsg").textContent="ใส่ชื่อของคุณแล้วกด เข้าร่วมกลุ่ม"}
else if(S.gOn&&(S.gName||S.gView)&&roomOk(S.gRoom||"")&&fbBase()){grp.on=true;grp.name=S.gName||"ผู้ชม";grp.room=S.gRoom;gLoop()}
if(!hm)renderGroup();
setInterval(tick,1000);tick();
regSW();
})();
