import * as THREE from '../libs/three.module.js';
import { GLTFLoader } from '../libs/examples/jsm/loaders/GLTFLoader.js';
import { OrbitControls } from '../libs/examples/jsm/controls/OrbitControls.js';

const $ = s => document.querySelector(s);
const canvasWrap = $('#canvas-wrap');
const modelSelect = $('#modelSelect');
const reloadModels = $('#reloadModels');
const meshRows = $('#meshRows');
const metalInput = $('#metal');
const roughInput = $('#rough');
const clearcoatInput = $('#clearcoat');
const metalVal = $('#metalVal');
const roughVal = $('#roughVal');
const clearcoatVal = $('#clearcoatVal');
const applyBtn = $('#applyBtn');
const resetBtn = $('#resetBtn');
const saveBtn = $('#saveBtn');
const saveLocalBtn = $('#saveLocalBtn');
const loadLocalBtn = $('#loadLocalBtn');
const opStatus = $('#opStatus');
const statusLive = $('#statusLive');
const modelFileName = $('#modelFileName');

const STORAGE_KEYS = { selectedModelUrl: 'bcs_selectedModelUrl_js_ac', selectedMeshNames: 'bcs_selectedMeshNames_js_ac' };
const MODELS_JSON_PATH = './models.json';
const MODELS_BASE = './models';

const DPR = Math.min(window.devicePixelRatio || 1, 2);
function safeLog(...a){ try{ console.log(...a); }catch(e){} }
function setStatus(msg, isErr=false){
  try{
    if(opStatus) { opStatus.textContent = msg; opStatus.style.color = isErr ? 'crimson' : 'var(--muted)'; }
    if(statusLive) statusLive.textContent = msg;
  }catch(e){}
  safeLog(msg);
}

let renderer, scene, camera, controls, loader;
let modelsJson = [];
let currentModel = null;
const meshMap = new Map();
const originalMaterials = new Map();
const clonedMaterials = new Map();
let currentModelUseEnvMap = true;
let liveApply = true;

/* ---------- Color utils: Lab <-> sRGB ---------- */
function srgbToLinear(c){ c = c/255; return c <= 0.04045 ? c/12.92 : Math.pow((c+0.055)/1.055, 2.4); }
function linearToSrgb(c){ return c <= 0.0031308 ? 12.92*c : 1.055*Math.pow(c,1/2.4)-0.055; }
function rgbToXyz(r,g,b){
  // sRGB D65
  const R = srgbToLinear(r), G = srgbToLinear(g), B = srgbToLinear(b);
  const x = R*0.4124564 + G*0.3575761 + B*0.1804375;
  const y = R*0.2126729 + G*0.7151522 + B*0.0721750;
  const z = R*0.0193339 + G*0.1191920 + B*0.9503041;
  return {x,y,z};
}
function xyzToRgb(x,y,z){
  let R =  3.2404542*x -1.5371385*y -0.4985314*z;
  let G = -0.9692660*x +1.8760108*y +0.0415560*z;
  let B =  0.0556434*x -0.2040259*y +1.0572252*z;
  R = Math.min(1, Math.max(0, linearToSrgb(R)));
  G = Math.min(1, Math.max(0, linearToSrgb(G)));
  B = Math.min(1, Math.max(0, linearToSrgb(B)));
  return { r: Math.round(R*255), g: Math.round(G*255), b: Math.round(B*255) };
}
function fLab(t){ const d = 6/29; return t > d*d*d ? Math.cbrt(t) : (t/(3*d*d) + 4/29); }
function finvLab(t){ const d = 6/29; return t > d ? t*t*t : 3*d*d*(t - 4/29); }
function xyzToLab(x,y,z){
  // D65 reference white
  const Xr=0.95047, Yr=1.00000, Zr=1.08883;
  const fx=fLab(x/Xr), fy=fLab(y/Yr), fz=fLab(z/Zr);
  const L=116*fy-16, a=500*(fx-fy), b=200*(fy-fz);
  return { L, a, b };
}
function labToXyz(L,a,b){
  const fy=(L+16)/116; const fx=fy + a/500; const fz=fy - b/200;
  const Xr=0.95047, Yr=1.00000, Zr=1.08883;
  const x= Xr*finvLab(fx); const y= Yr*finvLab(fy); const z= Zr*finvLab(fz);
  return { x,y,z };
}
function rgbHexToRgb(hex){
  const m = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex||'');
  if(!m) return {r:255,g:255,b:255};
  return { r: parseInt(m[1],16), g: parseInt(m[2],16), b: parseInt(m[3],16) };
}
function rgbToHex(r,g,b){ return '#' + [r,g,b].map(v=>{
  const s = Math.max(0,Math.min(255,v|0)).toString(16).padStart(2,'0');
  return s;
}).join(''); }
function hexToLab(hex){ const {r,g,b}=rgbHexToRgb(hex); const xyz=rgbToXyz(r,g,b); return xyzToLab(xyz.x, xyz.y, xyz.z); }
function labToHex(L,a,b){ const xyz=labToXyz(L,a,b); const rgb=xyzToRgb(xyz.x,xyz.y,xyz.z); return rgbToHex(rgb.r,rgb.g,rgb.b); }
/* ---------- Color utils: HSL <-> RGB ---------- */
function rgbToHsl(r,g,b){
  r /= 255; g /= 255; b /= 255;
  const max = Math.max(r, g, b), min = Math.min(r, g, b);
  let h, s, l = (max + min) / 2;
  if(max === min){
    h = s = 0; // achromatic
  } else {
    const d = max - min;
    s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
    switch(max){
      case r: h = ((g - b) / d + (g < b ? 6 : 0)) / 6; break;
      case g: h = ((b - r) / d + 2) / 6; break;
      case b: h = ((r - g) / d + 4) / 6; break;
    }
  }
  return { h: Math.round(h * 360), s: Math.round(s * 100), l: Math.round(l * 100) };
}
function hslToRgb(h,s,l){
  h /= 360; s /= 100; l /= 100;
  let r, g, b;
  if(s === 0){
    r = g = b = l; // achromatic
  } else {
    const hue2rgb = (p, q, t) => {
      if(t < 0) t += 1;
      if(t > 1) t -= 1;
      if(t < 1/6) return p + (q - p) * 6 * t;
      if(t < 1/2) return q;
      if(t < 2/3) return p + (q - p) * (2/3 - t) * 6;
      return p;
    };
    const q = l < 0.5 ? l * (1 + s) : l + s - l * s;
    const p = 2 * l - q;
    r = hue2rgb(p, q, h + 1/3);
    g = hue2rgb(p, q, h);
    b = hue2rgb(p, q, h - 1/3);
  }
  return { r: Math.round(r * 255), g: Math.round(g * 255), b: Math.round(b * 255) };
}
function hexToHsl(hex){ const {r,g,b}=rgbHexToRgb(hex); return rgbToHsl(r,g,b); }
function hslToHex(h,s,l){ const rgb=hslToRgb(h,s,l); return rgbToHex(rgb.r,rgb.g,rgb.b); }

function makeModelUrl(filePath){
  if(!filePath) return filePath;
  if(/^https?:\/\//i.test(filePath)) return filePath;
  if(filePath.startsWith('/') || filePath.startsWith('./') || filePath.startsWith('../')) return filePath;
  return `${MODELS_BASE}/${filePath}`;
}

/* ---------- Three init ---------- */
function initThree(){
  renderer = new THREE.WebGLRenderer({ antialias:true, alpha:true });
  renderer.outputEncoding = THREE.sRGBEncoding;
  renderer.toneMapping = THREE.ACESFilmicToneMapping;
  renderer.toneMappingExposure = 1.0;
  // enable shadows
  try{ renderer.shadowMap.enabled = true; renderer.shadowMap.type = THREE.PCFSoftShadowMap; }catch(e){}
  renderer.setPixelRatio(DPR);
  renderer.setSize(400,300);
  const canvas = renderer.domElement;
  canvas.setAttribute('role','img');
  canvas.setAttribute('aria-label','3D ビューポート');
  canvasWrap.appendChild(canvas);

  scene = new THREE.Scene();
  scene.background = new THREE.Color(0xffffff);

  camera = new THREE.PerspectiveCamera(45, 16/9, 0.01, 1000);
  camera.position.set(0, 1.6, 3);

  controls = new OrbitControls(camera, canvas);
  controls.enableDamping = true;

  loader = new GLTFLoader();

  // add lights here — after scene exists
  addDefaultLights();
}

/* ---------- unloadCurrent (追加) ---------- */
function unloadCurrent(){
  try{
    if(!currentModel) return;
    scene.remove(currentModel);
    currentModel.traverse(n=>{
      if(n.isMesh){
        try{ if(n.geometry) n.geometry.dispose(); }catch(e){}
        const mats = Array.isArray(n.material) ? n.material : [n.material];
        mats.forEach(m=>{
          try{ if(m && m.map) m.map.dispose(); }catch(e){}
          try{ if(m && m.dispose) m.dispose(); }catch(e){}
        });
      }
    });
  }catch(e){ safeLog('unloadCurrent', e); }
  currentModel = null;
  meshMap.clear();
  originalMaterials.clear();
  clonedMaterials.clear();
  if(meshRows) meshRows.innerHTML = '';
  if(modelFileName) modelFileName.textContent = '';
  setStatus('モデルをアンロードしました');
}

/* ---------- lights / ground ---------- */
function addDefaultLights(){
  if(typeof scene === 'undefined' || !scene) { safeLog('addDefaultLights: scene not ready'); return; }
  const hemi = new THREE.HemisphereLight(0xffffff, 0x444444, 0.5); scene.add(hemi);
  const dir = new THREE.DirectionalLight(0xffffff, 1.3);
  dir.position.set(0,4.5,1.0);
  try{
    dir.castShadow = true;
    dir.shadow.mapSize.width = 2048;
    dir.shadow.mapSize.height = 2048;
    dir.shadow.bias = -0.0005;
    dir.shadow.radius = 2;
    const cam = dir.shadow.camera;
    cam.near = 0.1; cam.far = 50;
    cam.left = -10; cam.right = 10; cam.top = 10; cam.bottom = -10;
  }catch(e){}
  scene.add(dir); scene.add(dir.target);
  const rim = new THREE.DirectionalLight(0xffffff, 0.15); rim.position.set(0,2.5,-2); scene.add(rim);

  const baseFloorSize = 40;
  if(!scene.getObjectByName('__bcs_ground')){
    const groundMat = new THREE.ShadowMaterial({ opacity: 0.5 });
    const ground = new THREE.Mesh(new THREE.PlaneGeometry(baseFloorSize, baseFloorSize), groundMat);
    ground.rotation.x = -Math.PI/2; ground.position.y = -0.01; ground.receiveShadow = true;
    ground.name = '__bcs_ground';
    scene.add(ground);
  }
}

function updateDynamicEnvMap(enable=true){
  try{
    if(!enable){ scene.environment = null; return; }
    const cubeRenderTarget = new THREE.WebGLCubeRenderTarget(256, { generateMipmaps:true, minFilter:THREE.LinearMipmapLinearFilter, encoding:THREE.sRGBEncoding });
    const cubeCamera = new THREE.CubeCamera(0.1, 1000, cubeRenderTarget);
    const center = new THREE.Vector3();
    if(currentModel){
      const box = new THREE.Box3().setFromObject(currentModel);
      box.getCenter(center);
    } else {
      center.set(0,1,0);
    }
    cubeCamera.position.copy(center);
    scene.add(cubeCamera);
    cubeCamera.update(renderer, scene);
    scene.environment = cubeRenderTarget.texture;
    scene.remove(cubeCamera);
  }catch(e){ safeLog('updateDynamicEnvMap', e); }
}

/* ---------- populateModelSelect (既存) ---------- */
function populateModelSelect(){
  if(!modelSelect) return;
  modelSelect.innerHTML = '';
  const placeholder = document.createElement('option');
  placeholder.value = '';
  placeholder.textContent = '車体モデルを選択…';
  placeholder.disabled = true; placeholder.selected = true;
  modelSelect.appendChild(placeholder);

  modelsJson.forEach((m, idx) => {
    const url = (m.file && (m.file.startsWith('./') || m.file.startsWith('/') || /^https?:\/\//.test(m.file))) ? m.file : makeModelUrl(m.file);
    const opt = document.createElement('option');
    opt.value = url || '';
    opt.textContent = m.label || (m.file || `model_${idx}`);
    opt.dataset.index = String(idx);
    modelSelect.appendChild(opt);
  });

  try{
    const saved = localStorage.getItem(STORAGE_KEYS.selectedModelUrl);
    if(saved){
      const opt = Array.from(modelSelect.options).find(o => o.value === saved);
      if(opt) modelSelect.value = saved;
    }
  }catch(e){ safeLog('populateModelSelect persist read', e); }
}

/* ---------- mesh UI and material helpers (existing) ---------- */

function resolveKeyToNames(key, nameToNodesMap){
  if(!key) return [];
  if(Array.isArray(key)){
    const out = [];
    key.forEach(k => {
      resolveKeyToNames(k, nameToNodesMap).forEach(n => { if(!out.includes(n)) out.push(n); });
    });
    return out;
  }
  const kstr = String(key);
  const out = [];
  if(nameToNodesMap.has(kstr)){
    (nameToNodesMap.get(kstr) || []).forEach(n => out.push(n.name || n.userData?.name || n.uuid || ''));
    return out;
  }
  for(const nodes of nameToNodesMap.values()){
    for(const n of nodes){
      const candidate = n.name || n.userData?.name || n.uuid;
      if(candidate === kstr) out.push(candidate);
    }
  }
  return out;
}

function createMeshRow(display, namesArray, initialHex){
  const row = document.createElement('div');
  row.className = 'meshRowItem';
  row.dataset.names = JSON.stringify(namesArray);

  const cellRb = document.createElement('div');
  cellRb.className = 'meshCellRb';
  const rb = document.createElement('input');
  rb.type = 'radio';
  rb.name = 'meshRadioGroup';
  rb.className = 'meshRadio';
  rb.setAttribute('aria-label', `${display} を選択`);
  rb.addEventListener('change', onMeshRowRadioChange);
  cellRb.appendChild(rb);

  const cellLbl = document.createElement('div');
  cellLbl.className = 'meshCellLbl';
  const lbl = document.createElement('div');
  lbl.className = 'meshLabel';
  lbl.textContent = display;
  lbl.tabIndex = 0;
  lbl.addEventListener('click', ()=> { rb.checked = true; rb.dispatchEvent(new Event('change')); });
  cellLbl.appendChild(lbl);

  const cellPicker = document.createElement('div');
  cellPicker.className = 'meshCellPicker';

  // 反映色のカラーピッカー
  const picker = document.createElement('input');
  picker.type = 'color';
  picker.className = 'meshColor';
  picker.value = initialHex || '#ffffff';
  picker.dataset.names = JSON.stringify(namesArray);
  picker.setAttribute('title', `${display} の色`);
  picker.addEventListener('input', onPerItemColorChange);
  // モバイル対応: 初期状態では非表示（必要に応じて表示）
  cellPicker.appendChild(picker);

  // RGBで選択ボタン
  const rgbBtn = document.createElement('button');
  rgbBtn.type = 'button';
  rgbBtn.className = 'btn labBtn';
  rgbBtn.textContent = 'RGB選択';
  rgbBtn.setAttribute('title', 'RGB形式で色を指定');
  rgbBtn.dataset.names = JSON.stringify(namesArray);
  rgbBtn.addEventListener('click', () => openRgbDialog(picker, namesArray));
  cellPicker.appendChild(rgbBtn);

  // HSLで選択ボタン
  const hslBtn = document.createElement('button');
  hslBtn.type = 'button';
  hslBtn.className = 'btn labBtn';
  hslBtn.textContent = 'HSL選択';
  hslBtn.setAttribute('title', 'HSL形式で色を指定');
  hslBtn.dataset.names = JSON.stringify(namesArray);
  hslBtn.addEventListener('click', () => openHslDialog(picker, namesArray));
  cellPicker.appendChild(hslBtn);

  // Lab形式ボタン
  const labBtn = document.createElement('button');
  labBtn.type = 'button';
  labBtn.className = 'btn labBtn';
  labBtn.textContent = 'Lab選択';
  labBtn.setAttribute('title', 'Lab形式で色を指定');
  labBtn.dataset.names = JSON.stringify(namesArray);
  labBtn.addEventListener('click', () => openLabDialog(picker, namesArray));
  cellPicker.appendChild(labBtn);

  row.appendChild(cellRb);
  row.appendChild(cellLbl);
  row.appendChild(cellPicker);
  if(meshRows) meshRows.appendChild(row);
  return row;
}

function createMeshHeader(){
  try{
    if(!meshRows) return;
    const headerRow = document.createElement('div');
    headerRow.className = 'meshRowHeader';

    const cellLbl = document.createElement('div');
    cellLbl.className = 'meshCellLbl';
    const lblLabel = document.createElement('div');
    lblLabel.className = 'meshHeaderLabel';
    lblLabel.textContent = '部位';
    cellLbl.appendChild(lblLabel);

    const cellRb = document.createElement('div');
    cellRb.className = 'meshCellRb';

    const cellPicker = document.createElement('div');
    cellPicker.className = 'meshCellPicker';
    const pickerLabel = document.createElement('div');
    pickerLabel.className = 'meshHeaderLabel';
    pickerLabel.textContent = '色の選択';
    cellPicker.appendChild(pickerLabel);

    headerRow.appendChild(cellLbl);
    headerRow.appendChild(cellRb);
    headerRow.appendChild(cellPicker);
    meshRows.appendChild(headerRow);
  }catch(e){ safeLog('createMeshHeader', e); }
}

function buildMeshMapAndUI(root, entry = {}){
  try{
    meshMap.clear();
    if(meshRows) {
      meshRows.innerHTML = '';
      createMeshHeader();
    }
    const nameToNodes = new Map();
    const meshes = [];
    root.traverse(n => { if(n.isMesh) meshes.push(n); });

    meshes.forEach(m=>{
      const actual = (typeof m.name === 'string' && m.name.length > 0) ? m.name : (m.userData?.name || m.uuid);
      if(!nameToNodes.has(actual)) nameToNodes.set(actual, []);
      nameToNodes.get(actual).push(m);
      meshMap.set(actual, { mesh: m, actualName: actual, displayName: actual, groupShowInUI: true });
    });

    if(entry && entry.nameMap && typeof entry.nameMap === 'object'){
      for(const key of Object.keys(entry.nameMap)){
        const mapVal = entry.nameMap[key];
        let displayVal = null;
        if(typeof mapVal === 'string') displayVal = mapVal;
        else if(mapVal && typeof mapVal === 'object' && typeof mapVal.display === 'string') displayVal = mapVal.display;
        if(!displayVal) continue;
        const resolved = resolveKeyToNames(key, nameToNodes);
        resolved.forEach(nm => { const rec = meshMap.get(nm); if(rec) rec.displayName = displayVal; });
      }
    }

    const groupsDef = (entry && entry.groups && typeof entry.groups === 'object') ? entry.groups : {};
    const processed = new Set();
    const uiList = [];

    for(const [gk, gv] of Object.entries(groupsDef)){
      let members = [], showInUI = true, displayName = gk;
      if(Array.isArray(gv)) { members = gv.slice(); showInUI = true; }
      else if(gv && typeof gv === 'object'){
        members = Array.isArray(gv.members) ? gv.members.slice() : (Array.isArray(gv)?gv.slice():[]);
        showInUI = (typeof gv.showInUI === 'boolean') ? gv.showInUI : true;
        if(typeof gv.display === 'string' && gv.display.trim()) displayName = gv.display;
      } else continue;

      const memberNames = [];
      members.forEach(mk => resolveKeyToNames(mk, nameToNodes).forEach(nm => { if(!memberNames.includes(nm)) memberNames.push(nm); }));
      memberNames.forEach(nm => { const rec = meshMap.get(nm); if(rec){ rec.groupDisplay = displayName; rec.groupKey = gk; rec.groupShowInUI = showInUI; processed.add(nm); }});

      const visible = memberNames.filter(nm => { const r = meshMap.get(nm); return r && r.groupShowInUI !== false; });
      if(visible.length) uiList.push({ displayName, names: visible.slice(), count: visible.length });
    }

    const remaining = new Map();
    meshMap.forEach((v,name)=>{
      if(processed.has(name)) return;
      if(v.groupShowInUI === false) return;
      if(entry && typeof entry.showUnaliased === 'boolean' && entry.showUnaliased === false) return;
      const display = v.displayName || v.actualName || name;
      if(!remaining.has(display)) remaining.set(display, { names: [] });
      remaining.get(display).names.push(name);
    });
    for(const [display, obj] of remaining.entries()) uiList.push({ displayName: display, names: obj.names.slice(), count: obj.names.length });

    // keep the order as defined (groups follow models.json order; others follow discovery order)
    uiList.forEach(item=>{
      let initial = '#ffffff';
      try{
        const first = item.names[0];
        const rec = meshMap.get(first);
        if(rec && rec.mesh){
          const m = Array.isArray(rec.mesh.material) ? rec.mesh.material[0] : rec.mesh.material;
          if(m && m.color) initial = '#' + (m.color.getHexString ? m.color.getHexString() : new THREE.Color(m.color).getHexString());
        }
      }catch(e){}
      createMeshRow(item.displayName, item.names, initial);
    });

    try{
      const saved = localStorage.getItem(STORAGE_KEYS.selectedMeshNames);
      let hasSelection = false;
      if(saved){
        const arr = JSON.parse(saved);
        if(Array.isArray(arr) && arr.length > 0){
          Array.from(meshRows.querySelectorAll('.meshRowItem')).forEach(r=>{
            try{
              const names = JSON.parse(r.dataset.names || '[]');
              const cb = r.querySelector('.meshRadio');
              if(cb && names.some(n => arr.includes(n))){
                cb.checked = true;
                hasSelection = true;
              }
            }catch(e){}
          });
        }
      }
      // If no saved selection, select first visible mesh
      if(!hasSelection){
        const firstRow = meshRows.querySelector('.meshRowItem');
        if(firstRow){
          const cb = firstRow.querySelector('.meshRadio');
          if(cb){
            cb.checked = true;
            cb.dispatchEvent(new Event('change'));
          }
        }
      }
    }catch(e){ safeLog('restore selection', e); }

    setStatus('UI 構築完了');
    // Resize panel to fit content
    resizeCanvasToAvailable();
    setTimeout(resizeCanvasToAvailable, 100);
  }catch(e){ safeLog('buildMeshMapAndUI error', e); setStatus('UI 構築失敗', true); }
}

function getCheckedNames(){
  const out = [];
  Array.from(meshRows.querySelectorAll('.meshRowItem')).forEach(r=>{
    try{
      const cb = r.querySelector('.meshRadio');
      if(cb && cb.checked){
        const names = JSON.parse(r.dataset.names || '[]');
        names.forEach(n => out.push(n));
      }
    }catch(e){}
  });
  return out;
}

function onMeshRowRadioChange(e){
  try{
    const cb = e.target;
    const names = getCheckedNames();
    try{ localStorage.setItem(STORAGE_KEYS.selectedMeshNames, JSON.stringify(names)); }catch(e){ safeLog('persist selection failed', e); }
    setStatus(`選択 ${names.length} 件`);
    if(names.length){
      names.forEach(n => console.log('selected mesh:', n));
    }
    if(currentModel && currentModel.userData && currentModel.userData.__sourceFile && modelFileName) modelFileName.textContent = currentModel.userData.__sourceFile;
    if(names.length === 1) syncGlobalUIFromSingle(names[0]);
  }catch(e){ safeLog('onMeshRowRadioChange', e); }
}

function onPerItemColorChange(e){
  try{
    const color = e.target.value;
    const names = JSON.parse(e.target.dataset.names || '[]');
    if(!Array.isArray(names) || !names.length) return;
    names.forEach(n => applyParamsToMeshByName(n, { color }));
    // Force render update after color change
    if(renderer && scene && camera){
      try{ controls.update(); renderer.render(scene, camera); }catch(e){}
    }
  }catch(e){ safeLog('onPerItemColorChange', e); }
}

function openLabDialog(picker, namesArray){
  try{
    const currentHex = picker.value || '#ffffff';
    const currentLab = hexToLab(currentHex);

    // create dialog overlay
    const overlay = document.createElement('div');
    overlay.className = 'labDialogOverlay';
    overlay.setAttribute('role','dialog');
    overlay.setAttribute('aria-modal','true');
    overlay.setAttribute('aria-label','Lab形式カラーピッカー');
    overlay.setAttribute('data-form-type', 'other');
    overlay.setAttribute('data-lpignore', 'true');

    const dialog = document.createElement('div');
    dialog.className = 'labDialog';
    dialog.setAttribute('data-form-type', 'other');
    dialog.setAttribute('data-lpignore', 'true');

    const title = document.createElement('h3');
    title.textContent = 'Lab形式で色を指定';
    title.style.margin = '0 0 16px 0';
    title.style.fontSize = '16px';
    title.style.fontWeight = '700';

    // Lab inputs
    const labInputsWrap = document.createElement('div');
    labInputsWrap.className = 'labDialogInputs';

    const labLRow = document.createElement('div');
    labLRow.className = 'labDialogRow';
    const labLLabel = document.createElement('label');
    labLLabel.textContent = 'L*:';
    labLLabel.style.minWidth = '40px';
    const labLSlider = document.createElement('input');
    labLSlider.type = 'range';
    labLSlider.min = '0';
    labLSlider.max = '100';
    labLSlider.step = '0.1';
    labLSlider.value = currentLab.L.toFixed(1);
    labLSlider.style.flex = '1';
    labLSlider.className = 'labDialogSlider';
    const labLInput = document.createElement('input');
    labLInput.type = 'number';
    labLInput.step = '0.1';
    labLInput.min = '0';
    labLInput.max = '100';
    labLInput.value = currentLab.L.toFixed(1);
    labLInput.style.width = '100px';
    labLInput.setAttribute('autocomplete', 'off');
    labLInput.setAttribute('data-form-type', 'other');
    labLInput.setAttribute('data-lpignore', 'true');
    labLInput.setAttribute('name', 'lab-l');
    labLInput.setAttribute('id', 'lab-l-input');
    // Prevent extension interference
    labLInput.addEventListener('focus', (e) => { e.stopPropagation(); }, true);
    labLInput.addEventListener('input', (e) => { e.stopPropagation(); }, true);
    labLRow.appendChild(labLLabel);
    labLRow.appendChild(labLSlider);
    labLRow.appendChild(labLInput);

    const labARow = document.createElement('div');
    labARow.className = 'labDialogRow';
    const labALabel = document.createElement('label');
    labALabel.textContent = 'a*:';
    labALabel.style.minWidth = '40px';
    const labASlider = document.createElement('input');
    labASlider.type = 'range';
    labASlider.min = '-128';
    labASlider.max = '127';
    labASlider.step = '1';
    labASlider.value = Math.round(currentLab.a);
    labASlider.style.flex = '1';
    labASlider.className = 'labDialogSlider';
    const labAInput = document.createElement('input');
    labAInput.type = 'number';
    labAInput.step = '1';
    labAInput.min = '-128';
    labAInput.max = '127';
    labAInput.value = Math.round(currentLab.a);
    labAInput.style.width = '100px';
    labAInput.setAttribute('autocomplete', 'off');
    labAInput.setAttribute('data-form-type', 'other');
    labAInput.setAttribute('data-lpignore', 'true');
    labAInput.setAttribute('name', 'lab-a');
    labAInput.setAttribute('id', 'lab-a-input');
    // Prevent extension interference
    labAInput.addEventListener('focus', (e) => { e.stopPropagation(); }, true);
    labAInput.addEventListener('input', (e) => { e.stopPropagation(); }, true);
    labARow.appendChild(labALabel);
    labARow.appendChild(labASlider);
    labARow.appendChild(labAInput);

    const labBRow = document.createElement('div');
    labBRow.className = 'labDialogRow';
    const labBLabel = document.createElement('label');
    labBLabel.textContent = 'b*:';
    labBLabel.style.minWidth = '40px';
    const labBSlider = document.createElement('input');
    labBSlider.type = 'range';
    labBSlider.min = '-128';
    labBSlider.max = '127';
    labBSlider.step = '1';
    labBSlider.value = Math.round(currentLab.b);
    labBSlider.style.flex = '1';
    labBSlider.className = 'labDialogSlider';
    const labBInput = document.createElement('input');
    labBInput.type = 'number';
    labBInput.step = '1';
    labBInput.min = '-128';
    labBInput.max = '127';
    labBInput.value = Math.round(currentLab.b);
    labBInput.style.width = '100px';
    labBInput.setAttribute('autocomplete', 'off');
    labBInput.setAttribute('data-form-type', 'other');
    labBInput.setAttribute('data-lpignore', 'true');
    labBInput.setAttribute('name', 'lab-b');
    labBInput.setAttribute('id', 'lab-b-input');
    // Prevent extension interference
    labBInput.addEventListener('focus', (e) => { e.stopPropagation(); }, true);
    labBInput.addEventListener('input', (e) => { e.stopPropagation(); }, true);
    labBRow.appendChild(labBLabel);
    labBRow.appendChild(labBSlider);
    labBRow.appendChild(labBInput);

    labInputsWrap.appendChild(labLRow);
    labInputsWrap.appendChild(labARow);
    labInputsWrap.appendChild(labBRow);

    // Preview
    const previewWrap = document.createElement('div');
    previewWrap.style.marginTop = '16px';
    previewWrap.style.display = 'flex';
    previewWrap.style.alignItems = 'center';
    previewWrap.style.gap = '12px';
    const previewLabel = document.createElement('span');
    previewLabel.textContent = 'プレビュー:';
    previewLabel.style.fontSize = '13px';
    const previewColor = document.createElement('div');
    previewColor.className = 'labDialogPreview';
    previewColor.style.width = '80px';
    previewColor.style.height = '40px';
    previewColor.style.border = '1px solid #ccc';
    previewColor.style.borderRadius = '6px';
    previewColor.style.backgroundColor = currentHex;
    const previewHex = document.createElement('input');
    previewHex.type = 'text';
    previewHex.value = currentHex;
    previewHex.style.fontSize = '12px';
    previewHex.style.fontFamily = 'monospace';
    previewHex.style.width = '80px';
    previewHex.style.padding = '4px 6px';
    previewHex.style.border = '1px solid #d0d7de';
    previewHex.style.borderRadius = '4px';
    previewHex.style.boxSizing = 'border-box';
    previewHex.setAttribute('autocomplete', 'off');
    previewHex.setAttribute('data-form-type', 'other');
    previewHex.setAttribute('data-lpignore', 'true');
    previewHex.setAttribute('name', 'lab-hex');
    previewHex.setAttribute('id', 'lab-hex-input');
    previewHex.addEventListener('focus', (e) => { e.stopPropagation(); }, true);
    previewHex.addEventListener('input', (e) => { e.stopPropagation(); }, true);
    previewWrap.appendChild(previewLabel);
    previewWrap.appendChild(previewColor);
    previewWrap.appendChild(previewHex);

    // Update preview function and apply to 3D model in real-time
    let rafPending = false;
    const updatePreview = () => {
      try{
        const L = Math.max(0, Math.min(100, parseFloat(labLInput.value) || 0));
        const a = Math.max(-128, Math.min(127, parseFloat(labAInput.value) || 0));
        const b = Math.max(-128, Math.min(127, parseFloat(labBInput.value) || 0));
        const hex = labToHex(L, a, b);
        previewColor.style.backgroundColor = hex;
        previewHex.value = hex;

        // Apply color to 3D model in real-time (throttled with requestAnimationFrame)
        if(!rafPending){
          rafPending = true;
          requestAnimationFrame(() => {
            rafPending = false;
            try{
              picker.value = hex;
              namesArray.forEach(n => applyParamsToMeshByName(n, { color: hex }));
              // Force render update after color change
              if(renderer && scene && camera){
                try{ controls.update(); renderer.render(scene, camera); }catch(e){}
              }
            }catch(e){ safeLog('updatePreview apply color', e); }
          });
        }
      }catch(e){ safeLog('updatePreview', e); }
    };

    // Update Lab values from HEX input and apply to 3D model in real-time
    let rafPendingHex = false;
    const updateLabFromHex = () => {
      try{
        const hexValue = previewHex.value.trim();
        if(!/^#[0-9A-Fa-f]{6}$/.test(hexValue)) return; // Invalid hex format
        const lab = hexToLab(hexValue);
        labLInput.value = lab.L.toFixed(1);
        labLSlider.value = lab.L.toFixed(1);
        labAInput.value = Math.round(lab.a);
        labASlider.value = Math.round(lab.a);
        labBInput.value = Math.round(lab.b);
        labBSlider.value = Math.round(lab.b);
        previewColor.style.backgroundColor = hexValue;

        // Apply color to 3D model in real-time (throttled with requestAnimationFrame)
        if(!rafPendingHex){
          rafPendingHex = true;
          requestAnimationFrame(() => {
            rafPendingHex = false;
            try{
              picker.value = hexValue;
              namesArray.forEach(n => applyParamsToMeshByName(n, { color: hexValue }));
              // Force render update after color change
              if(renderer && scene && camera){
                try{ controls.update(); renderer.render(scene, camera); }catch(e){}
              }
            }catch(e){ safeLog('updateLabFromHex apply color', e); }
          });
        }
      }catch(e){ safeLog('updateLabFromHex', e); }
    };

    // Sync slider and input
    labLSlider.addEventListener('input', () => {
      labLInput.value = labLSlider.value;
      updatePreview();
    });
    labLInput.addEventListener('input', () => {
      const val = Math.max(0, Math.min(100, parseFloat(labLInput.value) || 0));
      labLSlider.value = val;
      updatePreview();
    });

    labASlider.addEventListener('input', () => {
      labAInput.value = labASlider.value;
      updatePreview();
    });
    labAInput.addEventListener('input', () => {
      const val = Math.max(-128, Math.min(127, parseFloat(labAInput.value) || 0));
      labASlider.value = val;
      updatePreview();
    });

    labBSlider.addEventListener('input', () => {
      labBInput.value = labBSlider.value;
      updatePreview();
    });
    labBInput.addEventListener('input', () => {
      const val = Math.max(-128, Math.min(127, parseFloat(labBInput.value) || 0));
      labBSlider.value = val;
      updatePreview();
    });

    // Update Lab from HEX input
    previewHex.addEventListener('input', () => {
      updateLabFromHex();
    });
    previewHex.addEventListener('change', () => {
      updateLabFromHex();
    });

    // Buttons
    const btnWrap = document.createElement('div');
    btnWrap.style.marginTop = '20px';
    btnWrap.style.display = 'flex';
    btnWrap.style.gap = '8px';
    btnWrap.style.justifyContent = 'flex-end';

    const cancelBtn = document.createElement('button');
    cancelBtn.type = 'button';
    cancelBtn.className = 'btn';
    cancelBtn.textContent = 'キャンセル';
    cancelBtn.addEventListener('click', () => {
      document.body.removeChild(overlay);
    });

    const okBtn = document.createElement('button');
    okBtn.type = 'button';
    okBtn.className = 'btn';
    okBtn.textContent = 'OK';
    okBtn.style.fontWeight = '700';
    okBtn.addEventListener('click', () => {
      try{
        // Try to use HEX value if valid, otherwise use Lab values
        const hexValue = previewHex.value.trim();
        let hex;
        if(/^#[0-9A-Fa-f]{6}$/.test(hexValue)){
          hex = hexValue;
        } else {
          const L = Math.max(0, Math.min(100, parseFloat(labLInput.value) || 0));
          const a = Math.max(-128, Math.min(127, parseFloat(labAInput.value) || 0));
          const b = Math.max(-128, Math.min(127, parseFloat(labBInput.value) || 0));
          hex = labToHex(L, a, b);
        }
        picker.value = hex;
        namesArray.forEach(n => applyParamsToMeshByName(n, { color: hex }));
        // Force render update after color change
        if(renderer && scene && camera){
          try{ controls.update(); renderer.render(scene, camera); }catch(e){}
        }
        document.body.removeChild(overlay);
      }catch(e){ safeLog('labDialog OK', e); }
    });

    btnWrap.appendChild(cancelBtn);
    btnWrap.appendChild(okBtn);

    dialog.appendChild(title);
    dialog.appendChild(labInputsWrap);
    dialog.appendChild(previewWrap);
    dialog.appendChild(btnWrap);
    overlay.appendChild(dialog);

    // Close on overlay click
    overlay.addEventListener('click', (e) => {
      if(e.target === overlay) document.body.removeChild(overlay);
    });

    // Intercept focusin to avoid extension handlers
    overlay.addEventListener('focusin', (e) => {
      try{ e.stopImmediatePropagation(); }catch(err){}
    }, true);

    // Close on Escape
    const escHandler = (e) => {
      if(e.key === 'Escape'){
        document.body.removeChild(overlay);
        document.removeEventListener('keydown', escHandler);
      }
    };
    document.addEventListener('keydown', escHandler);

    document.body.appendChild(overlay);

    // Delay focus to avoid browser extension interference
    // Set readonly temporarily to prevent extension from analyzing the field
    labLInput.setAttribute('readonly', 'readonly');
    labAInput.setAttribute('readonly', 'readonly');
    labBInput.setAttribute('readonly', 'readonly');
    previewHex.setAttribute('readonly', 'readonly');

    setTimeout(() => {
      try{
        labLInput.removeAttribute('readonly');
        labAInput.removeAttribute('readonly');
        labBInput.removeAttribute('readonly');
        previewHex.removeAttribute('readonly');
        labLInput.focus();
        labLInput.select();
      }catch(e){ safeLog('labDialog focus', e); }
    }, 50);
  }catch(e){ safeLog('openLabDialog', e); }
}

function openRgbDialog(picker, namesArray){
  try{
    const currentHex = picker.value || '#ffffff';
    const currentRgb = rgbHexToRgb(currentHex);

    // create dialog overlay
    const overlay = document.createElement('div');
    overlay.className = 'labDialogOverlay';
    overlay.setAttribute('role','dialog');
    overlay.setAttribute('aria-modal','true');
    overlay.setAttribute('aria-label','RGB形式カラーピッカー');
    overlay.setAttribute('data-form-type', 'other');
    overlay.setAttribute('data-lpignore', 'true');

    const dialog = document.createElement('div');
    dialog.className = 'labDialog';
    dialog.setAttribute('data-form-type', 'other');
    dialog.setAttribute('data-lpignore', 'true');

    const title = document.createElement('h3');
    title.textContent = 'RGB形式で色を指定';
    title.style.margin = '0 0 16px 0';
    title.style.fontSize = '16px';
    title.style.fontWeight = '700';

    // RGB inputs
    const rgbInputsWrap = document.createElement('div');
    rgbInputsWrap.className = 'labDialogInputs';

    const rgbRRow = document.createElement('div');
    rgbRRow.className = 'labDialogRow';
    const rgbRLabel = document.createElement('label');
    rgbRLabel.textContent = 'R:';
    rgbRLabel.style.minWidth = '40px';
    const rgbRSlider = document.createElement('input');
    rgbRSlider.type = 'range';
    rgbRSlider.min = '0';
    rgbRSlider.max = '255';
    rgbRSlider.step = '1';
    rgbRSlider.value = currentRgb.r;
    rgbRSlider.style.flex = '1';
    rgbRSlider.className = 'labDialogSlider';
    const rgbRInput = document.createElement('input');
    rgbRInput.type = 'number';
    rgbRInput.step = '1';
    rgbRInput.min = '0';
    rgbRInput.max = '255';
    rgbRInput.value = currentRgb.r;
    rgbRInput.style.width = '100px';
    rgbRInput.setAttribute('autocomplete', 'off');
    rgbRInput.setAttribute('data-form-type', 'other');
    rgbRInput.setAttribute('data-lpignore', 'true');
    rgbRInput.setAttribute('name', 'rgb-r');
    rgbRInput.setAttribute('id', 'rgb-r-input');
    rgbRInput.addEventListener('focus', (e) => { e.stopPropagation(); }, true);
    rgbRInput.addEventListener('input', (e) => { e.stopPropagation(); }, true);
    rgbRRow.appendChild(rgbRLabel);
    rgbRRow.appendChild(rgbRSlider);
    rgbRRow.appendChild(rgbRInput);

    const rgbGRow = document.createElement('div');
    rgbGRow.className = 'labDialogRow';
    const rgbGLabel = document.createElement('label');
    rgbGLabel.textContent = 'G:';
    rgbGLabel.style.minWidth = '40px';
    const rgbGSlider = document.createElement('input');
    rgbGSlider.type = 'range';
    rgbGSlider.min = '0';
    rgbGSlider.max = '255';
    rgbGSlider.step = '1';
    rgbGSlider.value = currentRgb.g;
    rgbGSlider.style.flex = '1';
    rgbGSlider.className = 'labDialogSlider';
    const rgbGInput = document.createElement('input');
    rgbGInput.type = 'number';
    rgbGInput.step = '1';
    rgbGInput.min = '0';
    rgbGInput.max = '255';
    rgbGInput.value = currentRgb.g;
    rgbGInput.style.width = '100px';
    rgbGInput.setAttribute('autocomplete', 'off');
    rgbGInput.setAttribute('data-form-type', 'other');
    rgbGInput.setAttribute('data-lpignore', 'true');
    rgbGInput.setAttribute('name', 'rgb-g');
    rgbGInput.setAttribute('id', 'rgb-g-input');
    rgbGInput.addEventListener('focus', (e) => { e.stopPropagation(); }, true);
    rgbGInput.addEventListener('input', (e) => { e.stopPropagation(); }, true);
    rgbGRow.appendChild(rgbGLabel);
    rgbGRow.appendChild(rgbGSlider);
    rgbGRow.appendChild(rgbGInput);

    const rgbBRow = document.createElement('div');
    rgbBRow.className = 'labDialogRow';
    const rgbBLabel = document.createElement('label');
    rgbBLabel.textContent = 'B:';
    rgbBLabel.style.minWidth = '40px';
    const rgbBSlider = document.createElement('input');
    rgbBSlider.type = 'range';
    rgbBSlider.min = '0';
    rgbBSlider.max = '255';
    rgbBSlider.step = '1';
    rgbBSlider.value = currentRgb.b;
    rgbBSlider.style.flex = '1';
    rgbBSlider.className = 'labDialogSlider';
    const rgbBInput = document.createElement('input');
    rgbBInput.type = 'number';
    rgbBInput.step = '1';
    rgbBInput.min = '0';
    rgbBInput.max = '255';
    rgbBInput.value = currentRgb.b;
    rgbBInput.style.width = '100px';
    rgbBInput.setAttribute('autocomplete', 'off');
    rgbBInput.setAttribute('data-form-type', 'other');
    rgbBInput.setAttribute('data-lpignore', 'true');
    rgbBInput.setAttribute('name', 'rgb-b');
    rgbBInput.setAttribute('id', 'rgb-b-input');
    rgbBInput.addEventListener('focus', (e) => { e.stopPropagation(); }, true);
    rgbBInput.addEventListener('input', (e) => { e.stopPropagation(); }, true);
    rgbBRow.appendChild(rgbBLabel);
    rgbBRow.appendChild(rgbBSlider);
    rgbBRow.appendChild(rgbBInput);

    rgbInputsWrap.appendChild(rgbRRow);
    rgbInputsWrap.appendChild(rgbGRow);
    rgbInputsWrap.appendChild(rgbBRow);

    // Preview
    const previewWrap = document.createElement('div');
    previewWrap.style.marginTop = '16px';
    previewWrap.style.display = 'flex';
    previewWrap.style.alignItems = 'center';
    previewWrap.style.gap = '12px';
    const previewLabel = document.createElement('span');
    previewLabel.textContent = 'プレビュー:';
    previewLabel.style.fontSize = '13px';
    const previewColor = document.createElement('div');
    previewColor.className = 'labDialogPreview';
    previewColor.style.width = '80px';
    previewColor.style.height = '40px';
    previewColor.style.border = '1px solid #ccc';
    previewColor.style.borderRadius = '6px';
    previewColor.style.backgroundColor = currentHex;
    const previewHex = document.createElement('input');
    previewHex.type = 'text';
    previewHex.value = currentHex;
    previewHex.style.fontSize = '12px';
    previewHex.style.fontFamily = 'monospace';
    previewHex.style.width = '80px';
    previewHex.style.padding = '4px 6px';
    previewHex.style.border = '1px solid #d0d7de';
    previewHex.style.borderRadius = '4px';
    previewHex.style.boxSizing = 'border-box';
    previewHex.setAttribute('autocomplete', 'off');
    previewHex.setAttribute('data-form-type', 'other');
    previewHex.setAttribute('data-lpignore', 'true');
    previewHex.setAttribute('name', 'rgb-hex');
    previewHex.setAttribute('id', 'rgb-hex-input');
    previewHex.addEventListener('focus', (e) => { e.stopPropagation(); }, true);
    previewHex.addEventListener('input', (e) => { e.stopPropagation(); }, true);
    previewWrap.appendChild(previewLabel);
    previewWrap.appendChild(previewColor);
    previewWrap.appendChild(previewHex);

    // Update preview function and apply to 3D model in real-time
    let rafPending = false;
    const updatePreview = () => {
      try{
        const r = Math.max(0, Math.min(255, parseInt(rgbRInput.value) || 0));
        const g = Math.max(0, Math.min(255, parseInt(rgbGInput.value) || 0));
        const b = Math.max(0, Math.min(255, parseInt(rgbBInput.value) || 0));
        const hex = rgbToHex(r, g, b);
        previewColor.style.backgroundColor = hex;
        previewHex.value = hex;
        // Apply color to 3D model in real-time (throttled with requestAnimationFrame)
        if(!rafPending){
          rafPending = true;
          requestAnimationFrame(() => {
            rafPending = false;
            try{
              picker.value = hex;
              namesArray.forEach(n => applyParamsToMeshByName(n, { color: hex }));
              // Force render update after color change
              if(renderer && scene && camera){
                try{ controls.update(); renderer.render(scene, camera); }catch(e){}
              }
            }catch(e){ safeLog('updatePreview apply color', e); }
          });
        }
      }catch(e){ safeLog('updatePreview', e); }
    };

    // Update RGB values from HEX input and apply to 3D model in real-time
    let rafPendingHex = false;
    const updateRgbFromHex = () => {
      try{
        const hexValue = previewHex.value.trim();
        if(!/^#[0-9A-Fa-f]{6}$/.test(hexValue)) return; // Invalid hex format
        const rgb = rgbHexToRgb(hexValue);
        rgbRInput.value = rgb.r;
        rgbRSlider.value = rgb.r;
        rgbGInput.value = rgb.g;
        rgbGSlider.value = rgb.g;
        rgbBInput.value = rgb.b;
        rgbBSlider.value = rgb.b;
        previewColor.style.backgroundColor = hexValue;
        // Apply color to 3D model in real-time (throttled with requestAnimationFrame)
        if(!rafPendingHex){
          rafPendingHex = true;
          requestAnimationFrame(() => {
            rafPendingHex = false;
            try{
              picker.value = hexValue;
              namesArray.forEach(n => applyParamsToMeshByName(n, { color: hexValue }));
              // Force render update after color change
              if(renderer && scene && camera){
                try{ controls.update(); renderer.render(scene, camera); }catch(e){}
              }
            }catch(e){ safeLog('updateRgbFromHex apply color', e); }
          });
        }
      }catch(e){ safeLog('updateRgbFromHex', e); }
    };

    // Sync slider and input
    rgbRSlider.addEventListener('input', () => {
      rgbRInput.value = rgbRSlider.value;
      updatePreview();
    });
    rgbRInput.addEventListener('input', () => {
      const val = Math.max(0, Math.min(255, parseInt(rgbRInput.value) || 0));
      rgbRSlider.value = val;
      updatePreview();
    });

    rgbGSlider.addEventListener('input', () => {
      rgbGInput.value = rgbGSlider.value;
      updatePreview();
    });
    rgbGInput.addEventListener('input', () => {
      const val = Math.max(0, Math.min(255, parseInt(rgbGInput.value) || 0));
      rgbGSlider.value = val;
      updatePreview();
    });

    rgbBSlider.addEventListener('input', () => {
      rgbBInput.value = rgbBSlider.value;
      updatePreview();
    });
    rgbBInput.addEventListener('input', () => {
      const val = Math.max(0, Math.min(255, parseInt(rgbBInput.value) || 0));
      rgbBSlider.value = val;
      updatePreview();
    });

    // Update RGB from HEX input
    previewHex.addEventListener('input', () => {
      updateRgbFromHex();
    });
    previewHex.addEventListener('change', () => {
      updateRgbFromHex();
    });

    // Buttons
    const btnWrap = document.createElement('div');
    btnWrap.style.marginTop = '20px';
    btnWrap.style.display = 'flex';
    btnWrap.style.gap = '8px';
    btnWrap.style.justifyContent = 'flex-end';

    const cancelBtn = document.createElement('button');
    cancelBtn.type = 'button';
    cancelBtn.className = 'btn';
    cancelBtn.textContent = 'キャンセル';
    cancelBtn.addEventListener('click', () => {
      document.body.removeChild(overlay);
    });

    const okBtn = document.createElement('button');
    okBtn.type = 'button';
    okBtn.className = 'btn';
    okBtn.textContent = 'OK';
    okBtn.style.fontWeight = '700';
    okBtn.addEventListener('click', () => {
      try{
        // Try to use HEX value if valid, otherwise use RGB values
        const hexValue = previewHex.value.trim();
        let hex;
        if(/^#[0-9A-Fa-f]{6}$/.test(hexValue)){
          hex = hexValue;
        } else {
          const r = Math.max(0, Math.min(255, parseInt(rgbRInput.value) || 0));
          const g = Math.max(0, Math.min(255, parseInt(rgbGInput.value) || 0));
          const b = Math.max(0, Math.min(255, parseInt(rgbBInput.value) || 0));
          hex = rgbToHex(r, g, b);
        }
        picker.value = hex;
        namesArray.forEach(n => applyParamsToMeshByName(n, { color: hex }));
        // Force render update after color change
        if(renderer && scene && camera){
          try{ controls.update(); renderer.render(scene, camera); }catch(e){}
        }
        document.body.removeChild(overlay);
      }catch(e){ safeLog('rgbDialog OK', e); }
    });

    btnWrap.appendChild(cancelBtn);
    btnWrap.appendChild(okBtn);

    dialog.appendChild(title);
    dialog.appendChild(rgbInputsWrap);
    dialog.appendChild(previewWrap);
    dialog.appendChild(btnWrap);
    overlay.appendChild(dialog);

    // Close on overlay click
    overlay.addEventListener('click', (e) => {
      if(e.target === overlay) document.body.removeChild(overlay);
    });

    // Intercept focusin to avoid extension handlers
    overlay.addEventListener('focusin', (e) => {
      try{ e.stopImmediatePropagation(); }catch(err){}
    }, true);

    // Close on Escape
    const escHandler = (e) => {
      if(e.key === 'Escape'){
        document.body.removeChild(overlay);
        document.removeEventListener('keydown', escHandler);
      }
    };
    document.addEventListener('keydown', escHandler);

    document.body.appendChild(overlay);

    // Delay focus to avoid browser extension interference
    rgbRInput.setAttribute('readonly', 'readonly');
    rgbGInput.setAttribute('readonly', 'readonly');
    rgbBInput.setAttribute('readonly', 'readonly');
    previewHex.setAttribute('readonly', 'readonly');

    setTimeout(() => {
      try{
        rgbRInput.removeAttribute('readonly');
        rgbGInput.removeAttribute('readonly');
        rgbBInput.removeAttribute('readonly');
        previewHex.removeAttribute('readonly');
        rgbRInput.focus();
        rgbRInput.select();
      }catch(e){ safeLog('rgbDialog focus', e); }
    }, 50);
  }catch(e){ safeLog('openRgbDialog', e); }
}

function openHslDialog(picker, namesArray){
  try{
    const currentHex = picker.value || '#ffffff';
    const currentHsl = hexToHsl(currentHex);

    // create dialog overlay
    const overlay = document.createElement('div');
    overlay.className = 'labDialogOverlay';
    overlay.setAttribute('role','dialog');
    overlay.setAttribute('aria-modal','true');
    overlay.setAttribute('aria-label','HSL形式カラーピッカー');
    overlay.setAttribute('data-form-type', 'other');
    overlay.setAttribute('data-lpignore', 'true');

    const dialog = document.createElement('div');
    dialog.className = 'labDialog';
    dialog.setAttribute('data-form-type', 'other');
    dialog.setAttribute('data-lpignore', 'true');

    const title = document.createElement('h3');
    title.textContent = 'HSL形式で色を指定';
    title.style.margin = '0 0 16px 0';
    title.style.fontSize = '16px';
    title.style.fontWeight = '700';

    // HSL inputs
    const hslInputsWrap = document.createElement('div');
    hslInputsWrap.className = 'labDialogInputs';

    const hslHRow = document.createElement('div');
    hslHRow.className = 'labDialogRow';
    const hslHLabel = document.createElement('label');
    hslHLabel.textContent = 'H:';
    hslHLabel.style.minWidth = '40px';
    const hslHSlider = document.createElement('input');
    hslHSlider.type = 'range';
    hslHSlider.min = '0';
    hslHSlider.max = '360';
    hslHSlider.step = '1';
    hslHSlider.value = currentHsl.h;
    hslHSlider.style.flex = '1';
    hslHSlider.className = 'labDialogSlider';
    const hslHInput = document.createElement('input');
    hslHInput.type = 'number';
    hslHInput.step = '1';
    hslHInput.min = '0';
    hslHInput.max = '360';
    hslHInput.value = currentHsl.h;
    hslHInput.style.width = '100px';
    hslHInput.setAttribute('autocomplete', 'off');
    hslHInput.setAttribute('data-form-type', 'other');
    hslHInput.setAttribute('data-lpignore', 'true');
    hslHInput.setAttribute('name', 'hsl-h');
    hslHInput.setAttribute('id', 'hsl-h-input');
    hslHInput.addEventListener('focus', (e) => { e.stopPropagation(); }, true);
    hslHInput.addEventListener('input', (e) => { e.stopPropagation(); }, true);
    hslHRow.appendChild(hslHLabel);
    hslHRow.appendChild(hslHSlider);
    hslHRow.appendChild(hslHInput);

    const hslSRow = document.createElement('div');
    hslSRow.className = 'labDialogRow';
    const hslSLabel = document.createElement('label');
    hslSLabel.textContent = 'S:';
    hslSLabel.style.minWidth = '40px';
    const hslSSlider = document.createElement('input');
    hslSSlider.type = 'range';
    hslSSlider.min = '0';
    hslSSlider.max = '100';
    hslSSlider.step = '1';
    hslSSlider.value = currentHsl.s;
    hslSSlider.style.flex = '1';
    hslSSlider.className = 'labDialogSlider';
    const hslSInput = document.createElement('input');
    hslSInput.type = 'number';
    hslSInput.step = '1';
    hslSInput.min = '0';
    hslSInput.max = '100';
    hslSInput.value = currentHsl.s;
    hslSInput.style.width = '100px';
    hslSInput.setAttribute('autocomplete', 'off');
    hslSInput.setAttribute('data-form-type', 'other');
    hslSInput.setAttribute('data-lpignore', 'true');
    hslSInput.setAttribute('name', 'hsl-s');
    hslSInput.setAttribute('id', 'hsl-s-input');
    hslSInput.addEventListener('focus', (e) => { e.stopPropagation(); }, true);
    hslSInput.addEventListener('input', (e) => { e.stopPropagation(); }, true);
    hslSRow.appendChild(hslSLabel);
    hslSRow.appendChild(hslSSlider);
    hslSRow.appendChild(hslSInput);

    const hslLRow = document.createElement('div');
    hslLRow.className = 'labDialogRow';
    const hslLLabel = document.createElement('label');
    hslLLabel.textContent = 'L:';
    hslLLabel.style.minWidth = '40px';
    const hslLSlider = document.createElement('input');
    hslLSlider.type = 'range';
    hslLSlider.min = '0';
    hslLSlider.max = '100';
    hslLSlider.step = '1';
    hslLSlider.value = currentHsl.l;
    hslLSlider.style.flex = '1';
    hslLSlider.className = 'labDialogSlider';
    const hslLInput = document.createElement('input');
    hslLInput.type = 'number';
    hslLInput.step = '1';
    hslLInput.min = '0';
    hslLInput.max = '100';
    hslLInput.value = currentHsl.l;
    hslLInput.style.width = '100px';
    hslLInput.setAttribute('autocomplete', 'off');
    hslLInput.setAttribute('data-form-type', 'other');
    hslLInput.setAttribute('data-lpignore', 'true');
    hslLInput.setAttribute('name', 'hsl-l');
    hslLInput.setAttribute('id', 'hsl-l-input');
    hslLInput.addEventListener('focus', (e) => { e.stopPropagation(); }, true);
    hslLInput.addEventListener('input', (e) => { e.stopPropagation(); }, true);
    hslLRow.appendChild(hslLLabel);
    hslLRow.appendChild(hslLSlider);
    hslLRow.appendChild(hslLInput);

    hslInputsWrap.appendChild(hslHRow);
    hslInputsWrap.appendChild(hslSRow);
    hslInputsWrap.appendChild(hslLRow);

    // Preview
    const previewWrap = document.createElement('div');
    previewWrap.className = 'labDialogPreviewWrap';
    previewWrap.style.display = 'flex';
    previewWrap.style.alignItems = 'center';
    previewWrap.style.gap = '12px';
    previewWrap.style.marginTop = '16px';

    const previewLabel = document.createElement('label');
    previewLabel.textContent = 'プレビュー:';
    previewLabel.style.fontSize = '14px';
    previewLabel.style.fontWeight = '600';

    const previewColor = document.createElement('div');
    previewColor.className = 'labDialogPreview';
    previewColor.style.width = '80px';
    previewColor.style.height = '40px';
    previewColor.style.border = '1px solid #ccc';
    previewColor.style.borderRadius = '6px';
    previewColor.style.backgroundColor = currentHex;
    const previewHex = document.createElement('input');
    previewHex.type = 'text';
    previewHex.value = currentHex;
    previewHex.style.fontSize = '12px';
    previewHex.style.fontFamily = 'monospace';
    previewHex.style.width = '80px';
    previewHex.style.padding = '4px 6px';
    previewHex.style.border = '1px solid #d0d7de';
    previewHex.style.borderRadius = '4px';
    previewHex.style.boxSizing = 'border-box';
    previewHex.setAttribute('autocomplete', 'off');
    previewHex.setAttribute('data-form-type', 'other');
    previewHex.setAttribute('data-lpignore', 'true');
    previewHex.setAttribute('name', 'hsl-hex');
    previewHex.setAttribute('id', 'hsl-hex-input');
    previewHex.addEventListener('focus', (e) => { e.stopPropagation(); }, true);
    previewHex.addEventListener('input', (e) => { e.stopPropagation(); }, true);
    previewWrap.appendChild(previewLabel);
    previewWrap.appendChild(previewColor);
    previewWrap.appendChild(previewHex);

    // Update preview function and apply to 3D model in real-time
    let rafPending = false;
    const updatePreview = () => {
      try{
        const h = Math.max(0, Math.min(360, parseInt(hslHInput.value) || 0));
        const s = Math.max(0, Math.min(100, parseInt(hslSInput.value) || 0));
        const l = Math.max(0, Math.min(100, parseInt(hslLInput.value) || 0));
        const hex = hslToHex(h, s, l);
        previewColor.style.backgroundColor = hex;
        previewHex.value = hex;
        // Apply color to 3D model in real-time (throttled with requestAnimationFrame)
        if(!rafPending){
          rafPending = true;
          requestAnimationFrame(() => {
            rafPending = false;
            try{
              picker.value = hex;
              namesArray.forEach(n => applyParamsToMeshByName(n, { color: hex }));
              // Force render update after color change
              if(renderer && scene && camera){
                try{ controls.update(); renderer.render(scene, camera); }catch(e){}
              }
            }catch(e){ safeLog('updatePreview error:', e); }
          });
        }
      }catch(e){ safeLog('updatePreview error:', e); }
    };

    // Update from HEX input
    const updateHslFromHex = () => {
      try{
        const hexValue = previewHex.value.trim();
        if(/^#[0-9A-Fa-f]{6}$/.test(hexValue)){
          const hsl = hexToHsl(hexValue);
          hslHInput.value = hsl.h;
          hslHSlider.value = hsl.h;
          hslSInput.value = hsl.s;
          hslSSlider.value = hsl.s;
          hslLInput.value = hsl.l;
          hslLSlider.value = hsl.l;
          previewColor.style.backgroundColor = hexValue;
          // Apply color to 3D model in real-time
          if(!rafPending){
            rafPending = true;
            requestAnimationFrame(() => {
              rafPending = false;
              try{
                picker.value = hexValue;
                namesArray.forEach(n => applyParamsToMeshByName(n, { color: hexValue }));
                // Force render update after color change
                if(renderer && scene && camera){
                  try{ controls.update(); renderer.render(scene, camera); }catch(e){}
                }
              }catch(e){ safeLog('updateHslFromHex error:', e); }
            });
          }
        }
      }catch(e){ safeLog('updateHslFromHex error:', e); }
    };

    // Sync sliders and inputs
    hslHSlider.addEventListener('input', () => {
      hslHInput.value = hslHSlider.value;
      updatePreview();
    });
    hslHInput.addEventListener('input', () => {
      hslHSlider.value = hslHInput.value;
      updatePreview();
    });
    hslSSlider.addEventListener('input', () => {
      hslSInput.value = hslSSlider.value;
      updatePreview();
    });
    hslSInput.addEventListener('input', () => {
      hslSSlider.value = hslSInput.value;
      updatePreview();
    });
    hslLSlider.addEventListener('input', () => {
      hslLInput.value = hslLSlider.value;
      updatePreview();
    });
    hslLInput.addEventListener('input', () => {
      hslLSlider.value = hslLInput.value;
      updatePreview();
    });

    // HEX input handler
    previewHex.addEventListener('input', () => {
      if(!rafPending){
        rafPending = true;
        requestAnimationFrame(() => {
          rafPending = false;
          updateHslFromHex();
        });
      }
    });

    // Buttons
    const btnWrap = document.createElement('div');
    btnWrap.className = 'labDialogButtons';
    btnWrap.style.display = 'flex';
    btnWrap.style.gap = '12px';
    btnWrap.style.justifyContent = 'flex-end';
    btnWrap.style.marginTop = '20px';

    const cancelBtn = document.createElement('button');
    cancelBtn.type = 'button';
    cancelBtn.className = 'btn';
    cancelBtn.textContent = 'キャンセル';
    cancelBtn.addEventListener('click', () => {
      document.body.removeChild(overlay);
    });

    const okBtn = document.createElement('button');
    okBtn.type = 'button';
    okBtn.className = 'btn';
    okBtn.textContent = 'OK';
    okBtn.style.fontWeight = '700';
    okBtn.addEventListener('click', () => {
      try{
        // Try to use HEX value if valid, otherwise use HSL values
        const hexValue = previewHex.value.trim();
        let hex;
        if(/^#[0-9A-Fa-f]{6}$/.test(hexValue)){
          hex = hexValue;
        } else {
          const h = Math.max(0, Math.min(360, parseInt(hslHInput.value) || 0));
          const s = Math.max(0, Math.min(100, parseInt(hslSInput.value) || 0));
          const l = Math.max(0, Math.min(100, parseInt(hslLInput.value) || 0));
          hex = hslToHex(h, s, l);
        }
        picker.value = hex;
        namesArray.forEach(n => applyParamsToMeshByName(n, { color: hex }));
        // Force render update after color change
        if(renderer && scene && camera){
          try{ controls.update(); renderer.render(scene, camera); }catch(e){}
        }
        document.body.removeChild(overlay);
      }catch(e){ safeLog('hslDialog OK', e); }
    });

    btnWrap.appendChild(cancelBtn);
    btnWrap.appendChild(okBtn);

    dialog.appendChild(title);
    dialog.appendChild(hslInputsWrap);
    dialog.appendChild(previewWrap);
    dialog.appendChild(btnWrap);
    overlay.appendChild(dialog);

    // Close on overlay click
    overlay.addEventListener('click', (e) => {
      if(e.target === overlay) document.body.removeChild(overlay);
    });

    // Intercept focusin to avoid extension handlers
    overlay.addEventListener('focusin', (e) => {
      try{ e.stopImmediatePropagation(); }catch(err){}
    }, true);

    // Close on Escape
    const escHandler = (e) => {
      if(e.key === 'Escape'){
        document.body.removeChild(overlay);
        document.removeEventListener('keydown', escHandler);
      }
    };
    document.addEventListener('keydown', escHandler);

    document.body.appendChild(overlay);

    // Focus first input after a short delay
    setTimeout(() => {
      try{
        hslHInput.removeAttribute('readonly');
        hslSInput.removeAttribute('readonly');
        hslLInput.removeAttribute('readonly');
        previewHex.removeAttribute('readonly');
        hslHInput.focus();
      }catch(e){}
    }, 100);
  }catch(e){ safeLog('openHslDialog', e); }
}

function syncGlobalUIFromSingle(meshName){
  try{
    const rec = meshMap.get(meshName);
    if(!rec || !rec.mesh) return;
    const primary = Array.isArray(rec.mesh.material) ? rec.mesh.material[0] : rec.mesh.material;
    if(primary && typeof primary.metalness === 'number'){ metalInput.value = primary.metalness; metalVal.value = primary.metalness.toFixed(2); }
    if(primary && typeof primary.roughness === 'number'){ roughInput.value = primary.roughness; roughVal.value = primary.roughness.toFixed(2); }
    if(primary && primary.isMeshPhysicalMaterial && typeof primary.clearcoat === 'number'){ clearcoatInput.value = primary.clearcoat; clearcoatVal.value = primary.clearcoat.toFixed(2); }
  }catch(e){ safeLog('syncGlobalUIFromSingle', e); }
}

function cloneMaterial(mesh){
  try{
    if(!mesh || !mesh.material) return null;
    if(clonedMaterials.has(mesh.name)) return clonedMaterials.get(mesh.name);
    if(!originalMaterials.has(mesh.name)) originalMaterials.set(mesh.name, mesh.material);
    const src = mesh.material;
    let cloned = Array.isArray(src) ? src.map(m => m.clone()) : src.clone();
    const ensureProps = (m, srcM) => {
      if(!m) return m;
      let material = m;
      try{
        // Convert MeshStandardMaterial to MeshPhysicalMaterial for clearcoat support
        if(m.isMeshStandardMaterial && !m.isMeshPhysicalMaterial){
          const physical = new THREE.MeshPhysicalMaterial();
          Object.keys(m).forEach(k => {
            try{ if(k !== 'type' && k !== 'isMeshStandardMaterial' && k !== 'isMaterial') physical[k] = m[k]; }catch(e){}
          });
          physical.needsUpdate = true;
          material = physical;
        }
        if(srcM && srcM.map){ material.map = srcM.map; try{ material.map.encoding = THREE.sRGBEncoding; }catch(e){} material.map.needsUpdate = true; }
        if(srcM && srcM.emissiveMap){ material.emissiveMap = srcM.emissiveMap; try{ material.emissiveMap.encoding = THREE.sRGBEncoding; }catch(e){} material.emissiveMap.needsUpdate = true; }
      }catch(e){ safeLog('ensureProps', e); }
      if(!material.color || !(material.color instanceof THREE.Color)) material.color = new THREE.Color(0xffffff);
      if(typeof material.roughness !== 'number') material.roughness = (typeof srcM?.roughness === 'number') ? srcM.roughness : 0.5;
      if(typeof material.metalness !== 'number') material.metalness = (typeof srcM?.metalness === 'number') ? srcM.metalness : 0.0;
      if(material.isMeshPhysicalMaterial){
        if(typeof material.clearcoat !== 'number') material.clearcoat = (typeof srcM?.clearcoat === 'number') ? srcM.clearcoat : 0.0;
        if(typeof material.clearcoatRoughness !== 'number') material.clearcoatRoughness = (typeof srcM?.clearcoatRoughness === 'number') ? srcM.clearcoatRoughness : 0.0;
      }
      material.needsUpdate = true;
      return material;
    };
    if(Array.isArray(cloned)){
      const srcArr = Array.isArray(src) ? src : [src];
      cloned = cloned.map((m,i) => ensureProps(m, srcArr[i]||srcArr[0]));
    } else {
      cloned = ensureProps(cloned, src);
    }
    mesh.material = cloned;
    clonedMaterials.set(mesh.name, cloned);
    return cloned;
  }catch(e){ safeLog('cloneMaterial', e); return null; }
}

function applyParamsToMeshByName(meshName, params){
  try{
    const rec = meshMap.get(meshName);
    if(!rec || !rec.mesh) return;
    const mesh = rec.mesh;
    const cloned = cloneMaterial(mesh);
    if(!cloned) return;
    const applyTo = m => {
      if(!m) return;
      const isPBR = ('metalness' in m) || ('roughness' in m);
      if(!m.color || !(m.color instanceof THREE.Color)) m.color = new THREE.Color(0xffffff);
      if(params.color){ try{ m.color.set(params.color); }catch(e){ safeLog('color set failed', e); } }
      if(isPBR){
        if(typeof params.metalness === 'number') m.metalness = params.metalness;
        if(typeof params.roughness === 'number') m.roughness = params.roughness;
      }
      if(m.isMeshPhysicalMaterial){
        if(typeof params.clearcoat === 'number') m.clearcoat = params.clearcoat;
      }
      try{ if(m.map){ try{ m.map.encoding = THREE.sRGBEncoding; }catch(e){} m.map.needsUpdate = true; } }catch(e){}
      m.needsUpdate = true;
    };
    if(Array.isArray(cloned)) cloned.forEach(applyTo); else applyTo(cloned);
    if(currentModelUseEnvMap) updateDynamicEnvMap(true);
    // Force render update after material change
    if(renderer && scene && camera){
      try{ controls.update(); renderer.render(scene, camera); }catch(e){}
    }
  }catch(e){ safeLog('applyParamsToMeshByName', e); }
}

function applyUIToSelection(){
  try{
    const names = getCheckedNames();
    if(names.length === 0){ alert('メッシュを選択してください'); return; }
    const params = { metalness: parseFloat(metalInput.value), roughness: parseFloat(roughInput.value), clearcoat: parseFloat(clearcoatInput.value) };
    names.forEach(n => applyParamsToMeshByName(n, params));
    setStatus(`適用: ${names.length} 件`);
  }catch(e){ safeLog('applyUIToSelection', e); }
}

function resetSelectedMeshes(){
  try{
    const names = getCheckedNames();
    if(names.length === 0){ alert('メッシュを選択してください'); return; }
    const restored = [];
    names.forEach(name => {
      const rec = meshMap.get(name);
      if(!rec || !rec.mesh) return;
      const mesh = rec.mesh;
      if(originalMaterials.has(name)){
        const orig = originalMaterials.get(name);
        mesh.material = orig;
        try{ const p = Array.isArray(mesh.material) ? mesh.material[0] : mesh.material; if(p) p.needsUpdate = true; }catch(e){}
        // Remove from clonedMaterials map to ensure fresh clone on next color change
        if(clonedMaterials.has(name)){
          clonedMaterials.delete(name);
        }
        restored.push(name);
      }
    });
    if(currentModelUseEnvMap) updateDynamicEnvMap(true);

    // Reset material parameters UI to default values
    if(metalInput && metalVal){
      metalInput.value = '0.85';
      metalVal.value = '0.85';
    }
    if(roughInput && roughVal){
      roughInput.value = '0.12';
      roughVal.value = '0.12';
    }
    if(clearcoatInput && clearcoatVal){
      clearcoatInput.value = '0.75';
      clearcoatVal.value = '0.75';
    }

    // Reset color pickers to white
    if(meshRows){
      Array.from(meshRows.querySelectorAll('.meshRowItem')).forEach(r => {
        try{
          const cb = r.querySelector('.meshRadio');
          if(cb && cb.checked){
            const picker = r.querySelector('.meshColor');
            if(picker){
              picker.value = '#ffffff';
              const names = JSON.parse(r.dataset.names || '[]');
              names.forEach(n => applyParamsToMeshByName(n, { color: '#ffffff' }));
            }
          }
        }catch(e){}
      });
    }

    setStatus(`リセット: ${restored.length} 件`);
  }catch(e){ safeLog('resetSelectedMeshes', e); alert('リセット中にエラーが発生しました。コンソールを確認してください。'); }
}

function buildPresetData(){
  const data = {
    version: '1.0',
    timestamp: new Date().toISOString(),
    modelUrl: modelSelect && modelSelect.value ? modelSelect.value : '',
    material: {
      metalness: parseFloat(metalInput.value) || 0,
      roughness: parseFloat(roughInput.value) || 0,
      clearcoat: parseFloat(clearcoatInput.value) || 0
    },
    meshes: []
  };
  try{
    Array.from(meshRows.querySelectorAll('.meshRowItem')).forEach(r => {
      try{
        const cb = r.querySelector('.meshRadio');
        const picker = r.querySelector('.meshColor');
        const lbl = r.querySelector('.meshLabel');
        const names = JSON.parse(r.dataset.names || '[]');
        if(!Array.isArray(names) || !names.length || !cb || !picker) return;
        data.meshes.push({ displayName: lbl ? lbl.textContent : '', meshNames: names, selected: !!cb.checked, color: picker.value||'#ffffff' });
      }catch(e){}
    });
  }catch(e){ safeLog('buildPresetData', e); }
  return data;
}

function saveToLocal(){
  try{
    const data = buildPresetData();
    localStorage.setItem('bcs3d_preset_v1', JSON.stringify(data));
    setStatus('ローカルに保存しました');
  }catch(e){ safeLog('saveToLocal', e); alert('ローカル保存に失敗しました'); }
}

async function loadFromLocal(){
  try{
    const raw = localStorage.getItem('bcs3d_preset_v1');
    if(!raw){ alert('保存データがありません'); return; }
    const data = JSON.parse(raw);
    if(!data || typeof data !== 'object'){ alert('保存データが不正です'); return; }
    // load model if different
    if(data.modelUrl && modelSelect && modelSelect.value !== data.modelUrl){
      const opt = Array.from(modelSelect.options).find(o=>o.value===data.modelUrl);
      if(opt){ modelSelect.value = data.modelUrl; await loadModel(data.modelUrl); }
    }
    // apply material UI
    if(data.material){
      if(typeof data.material.metalness === 'number'){ metalInput.value = data.material.metalness; metalVal.value = data.material.metalness.toFixed(2); }
      if(typeof data.material.roughness === 'number'){ roughInput.value = data.material.roughness; roughVal.value = data.material.roughness.toFixed(2); }
      if(typeof data.material.clearcoat === 'number'){ clearcoatInput.value = data.material.clearcoat; clearcoatVal.value = data.material.clearcoat.toFixed(2); }
    }
    // apply meshes (colors + selection)
    if(Array.isArray(data.meshes)){
      const rows = Array.from(meshRows.querySelectorAll('.meshRowItem'));
      data.meshes.forEach(mrec => {
        try{
          const row = rows.find(r=>{
            try{ const names = JSON.parse(r.dataset.names||'[]'); return Array.isArray(names) && Array.isArray(mrec.meshNames) && names.length===mrec.meshNames.length && names.every(n => mrec.meshNames.includes(n)); }catch(e){ return false; }
          });
          if(!row) return;
          const cb = row.querySelector('.meshRadio');
          const picker = row.querySelector('.meshColor');
          if(cb) cb.checked = !!mrec.selected;
          if(picker && typeof mrec.color === 'string'){ picker.value = mrec.color; const names = JSON.parse(row.dataset.names||'[]'); names.forEach(n => applyParamsToMeshByName(n, { color: mrec.color })); }
        }catch(e){}
      });
    }
    // apply global params to selected meshes
    applyUIToSelection();
    setStatus('ローカルから復元しました');
  }catch(e){ safeLog('loadFromLocal', e); alert('ローカル復元に失敗しました'); }
}

// Sync slider and number input for metalness
metalInput.addEventListener('input', e => {
  const val = parseFloat(e.target.value);
  metalVal.value = val.toFixed(2);
  if(liveApply) scheduleApplyOnce();
});
metalVal.addEventListener('input', e => {
  const val = Math.max(0, Math.min(1, parseFloat(e.target.value) || 0));
  metalInput.value = val;
  if(liveApply) scheduleApplyOnce();
});
metalVal.addEventListener('change', e => {
  const val = Math.max(0, Math.min(1, parseFloat(e.target.value) || 0));
  metalInput.value = val;
  metalVal.value = val.toFixed(2);
  if(liveApply) scheduleApplyOnce();
});

// Sync slider and number input for roughness
roughInput.addEventListener('input', e => {
  const val = parseFloat(e.target.value);
  roughVal.value = val.toFixed(2);
  if(liveApply) scheduleApplyOnce();
});
roughVal.addEventListener('input', e => {
  const val = Math.max(0, Math.min(1, parseFloat(e.target.value) || 0));
  roughInput.value = val;
  if(liveApply) scheduleApplyOnce();
});
roughVal.addEventListener('change', e => {
  const val = Math.max(0, Math.min(1, parseFloat(e.target.value) || 0));
  roughInput.value = val;
  roughVal.value = val.toFixed(2);
  if(liveApply) scheduleApplyOnce();
});

// Sync slider and number input for clearcoat
clearcoatInput.addEventListener('input', e => {
  const val = parseFloat(e.target.value);
  clearcoatVal.value = val.toFixed(2);
  if(liveApply) scheduleApplyOnce();
});
clearcoatVal.addEventListener('input', e => {
  const val = Math.max(0, Math.min(1, parseFloat(e.target.value) || 0));
  clearcoatInput.value = val;
  if(liveApply) scheduleApplyOnce();
});
clearcoatVal.addEventListener('change', e => {
  const val = Math.max(0, Math.min(1, parseFloat(e.target.value) || 0));
  clearcoatInput.value = val;
  clearcoatVal.value = val.toFixed(2);
  if(liveApply) scheduleApplyOnce();
});

let rafApplyScheduled = false;
function scheduleApplyOnce(){ if(rafApplyScheduled) return; rafApplyScheduled = true; requestAnimationFrame(()=>{ rafApplyScheduled = false; try{ applyUIToSelection(); }catch(e){ safeLog('scheduleApplyOnce', e); } }); }

if(applyBtn){ applyBtn.addEventListener('click', () => { liveApply = !liveApply; applyBtn.classList.toggle('active', liveApply); applyBtn.setAttribute('aria-pressed', String(liveApply)); applyBtn.textContent = liveApply ? 'ライブ適用中' : '適用'; applyUIToSelection(); setStatus(liveApply ? 'ライブ適用を開始しました' : 'ライブ適用を停止しました'); }); }
if(resetBtn){ resetBtn.addEventListener('click', () => resetSelectedMeshes()); }
if(saveLocalBtn){ saveLocalBtn.addEventListener('click', saveToLocal); }
if(loadLocalBtn){ loadLocalBtn.addEventListener('click', () => { loadFromLocal(); }); }

function saveCurrentData(){
  try{
    if(!currentModel){
      alert('モデルが読み込まれていません');
      return;
    }

    const data = {
      version: '1.0',
      timestamp: new Date().toISOString(),
      model: {
        url: modelSelect.value || '',
        fileName: currentModel.userData.__sourceFile || ''
      },
      material: {
        metalness: parseFloat(metalInput.value) || 0.85,
        roughness: parseFloat(roughInput.value) || 0.12,
        clearcoat: parseFloat(clearcoatInput.value) || 0.75
      },
      meshes: []
    };

    // Collect mesh data
    Array.from(meshRows.querySelectorAll('.meshRowItem')).forEach(r => {
      try{
        const cb = r.querySelector('.meshRadio');
        const picker = r.querySelector('.meshColor');
        const lbl = r.querySelector('.meshLabel');
        if(!cb || !picker || !lbl) return;

        const names = JSON.parse(r.dataset.names || '[]');
        if(!Array.isArray(names) || !names.length) return;

        const meshData = {
          displayName: lbl.textContent || '',
          meshNames: names,
          selected: cb.checked || false,
          color: picker.value || '#ffffff'
        };

        // Get current material values for selected meshes
        if(cb.checked && names.length > 0){
          const rec = meshMap.get(names[0]);
          if(rec && rec.mesh){
            const m = Array.isArray(rec.mesh.material) ? rec.mesh.material[0] : rec.mesh.material;
            if(m){
              meshData.material = {
                metalness: typeof m.metalness === 'number' ? m.metalness : null,
                roughness: typeof m.roughness === 'number' ? m.roughness : null,
                clearcoat: (m.isMeshPhysicalMaterial && typeof m.clearcoat === 'number') ? m.clearcoat : null
              };
            }
          }
        }

        data.meshes.push(meshData);
      }catch(e){ safeLog('saveCurrentData mesh', e); }
    });

    // Create download
    const jsonStr = JSON.stringify(data, null, 2);
    const blob = new Blob([jsonStr], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    const fileName = `bcs3d_${currentModel.userData.__sourceFile || 'model'}_${new Date().toISOString().slice(0,10)}.json`;
    a.href = url;
    a.download = fileName;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);

    setStatus('データを保存しました');
  }catch(e){
    safeLog('saveCurrentData', e);
    alert('データの保存中にエラーが発生しました');
  }
}

if(saveBtn){ saveBtn.addEventListener('click', saveCurrentData); }

function findEntryForUrl(url){ if(!modelsJson.length) return null; const name = (url||'').split('/').pop(); return modelsJson.find(e => ((e.file||'').split('/').pop() === name)) || null; }

function applyModelFixes(gltf, entry){
  try{
    if(!gltf || !gltf.scene) return;
    const modelFix = (entry && entry.fixOptions) ? entry.fixOptions : {};
    const perMesh = (entry && entry.perMesh) ? entry.perMesh : {};
    gltf.scene.traverse(node=>{
      if(!node.isMesh) return;
      let key = node.name || node.userData?.name || node.uuid;
      const meshOpts = Object.assign({}, modelFix, perMesh[node.name] || perMesh[node.uuid] || perMesh[key] || {});
      if(meshOpts.reverseWinding && node.geometry){
        try{
          const geom = node.geometry;
          if(geom.index){
            const idx = geom.index.array;
            for(let i=0;i<idx.length;i+=3){ const a=idx[i], b=idx[i+1], c=idx[i+2]; idx[i]=a; idx[i+1]=c; idx[i+2]=b; }
            geom.index.needsUpdate = true;
          }
          if(geom.attributes.normal){
            const n = geom.attributes.normal.array;
            for(let i=0;i<n.length;i++) n[i] = -n[i];
            geom.attributes.normal.needsUpdate = true;
          } else {
            try{ geom.computeVertexNormals(); if(geom.attributes.normal) geom.attributes.normal.needsUpdate=true; }catch(e){}
          }
        }catch(e){}
      }
      if(meshOpts.forceDoubleSided && node.material){ try{ node.material.side = THREE.DoubleSide; node.material.needsUpdate=true; }catch(e){} }
    });
  }catch(e){ safeLog('applyModelFixes', e); }
}

async function loadModel(url){
  if(!url){
    try{
      if(modelsJson && modelsJson.length){
        const first = modelsJson[0];
        const firstUrl = (first.file && (first.file.startsWith('./') || first.file.startsWith('/') || /^https?:\/\//.test(first.file))) ? first.file : makeModelUrl(first.file);
        if(firstUrl){
          try{ localStorage.setItem(STORAGE_KEYS.selectedModelUrl, firstUrl); }catch(e){}
          modelSelect.value = firstUrl;
          setStatus('モデルが未選択のため、最初のモデルを読み込みます...');
          await loadModel(firstUrl);
          return;
        }
      }
    }catch(e){ safeLog('fallback loadModel', e); }
    setStatus('モデル URL が空です', true);
    return;
  }
  setStatus('モデル読み込み中...');
  // Show progress overlay on canvas
  const progressOverlay = document.getElementById('canvasProgress');
  const progressText = progressOverlay ? progressOverlay.querySelector('.canvasProgressText') : null;
  const progressBarFill = progressOverlay ? progressOverlay.querySelector('.canvasProgressBarFill') : null;
  const progressPercent = progressOverlay ? progressOverlay.querySelector('.canvasProgressPercent') : null;
  if(progressOverlay) progressOverlay.style.display = 'flex';
  if(progressText) progressText.textContent = 'モデル読み込み中...';
  if(progressBarFill) progressBarFill.style.width = '0%';
  if(progressPercent) progressPercent.textContent = '0%';

  try{
    unloadCurrent();
    const entry = findEntryForUrl(url) || {};
    const gltf = await new Promise((resolve, reject) => {
      try{
        loader.load(url, resolve, (xhr)=>{
          try{
            if(xhr.total) {
              const percent = Math.round((xhr.loaded/xhr.total||0)*100);
              // UIのみ更新（コンソール出力しない）
              if(opStatus) { opStatus.textContent = `読み込み ${percent}%`; opStatus.style.color = 'var(--muted)'; }
              if(progressBarFill) progressBarFill.style.width = percent + '%';
              if(progressPercent) progressPercent.textContent = percent + '%';
            }
          }catch(e){}
        }, reject);
      }catch(e){ reject(e); }
    });
    if(!gltf || !gltf.scene) throw new Error('GLTF が不正です');
    currentModel = gltf.scene;
    try{ currentModel.userData.__sourceFile = (findEntryForUrl(url) && findEntryForUrl(url).file) ? findEntryForUrl(url).file : (url.split('/').pop()); if(modelFileName) modelFileName.textContent = currentModel.userData.__sourceFile; }catch(e){}
    scene.add(currentModel);
    // enable shadows on model meshes
    try{ currentModel.traverse(n=>{ if(n.isMesh){ n.castShadow = true; n.receiveShadow = true; } }); }catch(e){}
    currentModelUseEnvMap = !(entry && entry.useEnvMap === false);

    currentModel.traverse(n=>{ if(n.isMesh){ if(!originalMaterials.has(n.name)) originalMaterials.set(n.name, n.material); } });
    try{ applyModelFixes(gltf, entry); }catch(e){ safeLog('applyModelFixes failed', e); }

    buildMeshMapAndUI(currentModel, entry);

    try{
      // framing - モデルを可能な限り大きく表示（PC/スマホで最適化）
      const box = new THREE.Box3().setFromObject(currentModel);
      if(!box.isEmpty()){
        const size = box.getSize(new THREE.Vector3());
        const center = box.getCenter(new THREE.Vector3());
        const radius = Math.max(size.x, size.y, size.z) * 0.5;
        const isMobile = window.innerWidth <= 860;

        // PCとスマホで異なるマージンとカメラ位置を設定
        const margin = isMobile ? 1.01 : 1.005; // スマホは少し余裕を持たせる
        const heightOffset = isMobile ? Math.max(size.y * 0.01, radius * 0.01, 0.1) : Math.max(size.y * 0.015, radius * 0.015, 0.12);

        const fov = camera.fov * Math.PI / 180;
        const aspect = Math.max(0.1, renderer.domElement.clientWidth / Math.max(1, renderer.domElement.clientHeight));
        const distV = radius / Math.sin(fov * 0.5);
        const hfov = 2 * Math.atan(Math.tan(fov * 0.5) * aspect);
        const distH = radius / Math.sin(hfov * 0.5);

        // マージンを最小限にしてモデルを最大化
        const distance = Math.max(distV, distH) * margin;
        const camPos = new THREE.Vector3(center.x, center.y + heightOffset, center.z + distance);
        camera.position.copy(camPos);
        const targetOffsetY = Math.max(size.y * 0.005, 0.003);
        controls.target.set(center.x, center.y + targetOffsetY, center.z);
        controls.update();

        const relMargin = 0.0;
        const groundObj = scene.getObjectByName('__bcs_ground');
        if(groundObj){
          groundObj.position.y = box.min.y - relMargin;
          const footprint = Math.max(size.x, size.z);
          const floorSize = Math.max(footprint * 1.6, 1.0);
          const scaleFactor = floorSize / 40;
          groundObj.scale.set(scaleFactor,1,scaleFactor);
          groundObj.position.x = center.x; groundObj.position.z = center.z;
        }
      }
    }catch(e){ safeLog('frameModelToView failed', e); }

    if(currentModelUseEnvMap) updateDynamicEnvMap(true); else scene.environment = null;
    setStatus('モデル読み込み完了');
    // Hide progress overlay
    if(progressOverlay) progressOverlay.style.display = 'none';
    resizeCanvasToAvailable(); setTimeout(resizeCanvasToAvailable, 160);
  }catch(err){
    safeLog('loadModel failed', err);
    setStatus(`モデル読み込み失敗: ${err && err.message ? err.message : '不明'}`, true);
    // Hide progress overlay on error
    if(progressOverlay) progressOverlay.style.display = 'none';
  }
}

const css = getComputedStyle(document.documentElement);
const PANEL_H_MIN = parseInt(css.getPropertyValue('--panel-h-min')) || 120;
function getCssPanelMaxPx(vh){
  const cssMax = getComputedStyle(document.documentElement).getPropertyValue('--panel-h-max').trim();
  if(cssMax.endsWith('vh')) return Math.floor(vh * parseFloat(cssMax) / 100.0);
  if(cssMax.endsWith('px')) return parseInt(cssMax,10) || Math.floor(vh * 0.95);
  return Math.floor(vh * 0.95);
}

function resizeCanvasToAvailable(){
  try{
    const vw = window.innerWidth; const vh = window.innerHeight;
    const topbar = parseInt(getComputedStyle(document.documentElement).getPropertyValue('--topbar-h')) || 32;
    const reservedMargins = 4;
    const panelMaxPx = getCssPanelMaxPx(vh);
    const panelEl = document.getElementById('panel');
    const panelContentEl = document.getElementById('panelContent');

    // Calculate required panel height based on content
    let requiredPanelH = PANEL_H_MIN;
    if(panelContentEl && panelEl){
      // Temporarily set panel height to auto to measure content accurately
      const originalHeight = panelEl.style.height;
      const originalOverflow = panelEl.style.overflow;
      const originalMaxHeight = panelEl.style.maxHeight;
      panelEl.style.height = 'auto';
      panelEl.style.overflow = 'visible';
      panelEl.style.maxHeight = 'none';

      // Force a reflow to get accurate measurements
      void panelEl.offsetHeight;

      // Measure all content including buttons outside panelContent
      const contentHeight = panelContentEl.scrollHeight;
      const panelPadding = parseInt(getComputedStyle(document.documentElement).getPropertyValue('--panel-padding')) || 6;
      const panelMargin = 6; // margin from CSS

      // Check for buttons outside panelContent (save/load/reset buttons)
      let buttonsHeight = 0;
      const saveBtn = document.getElementById('saveLocalBtn');
      const loadBtn = document.getElementById('loadLocalBtn');
      const resetBtn = document.getElementById('resetBtn');
      if(saveBtn || loadBtn || resetBtn){
        const buttonsContainer = saveBtn ? saveBtn.parentElement : (loadBtn ? loadBtn.parentElement : (resetBtn ? resetBtn.parentElement : null));
        if(buttonsContainer && buttonsContainer !== panelContentEl){
          // Measure buttons container height including margins
          const buttonsRect = buttonsContainer.getBoundingClientRect();
          const buttonsStyle = getComputedStyle(buttonsContainer);
          const buttonsMarginTop = parseInt(buttonsStyle.marginTop) || 0;
          const buttonsMarginBottom = parseInt(buttonsStyle.marginBottom) || 0;
          buttonsHeight = buttonsRect.height + buttonsMarginTop + buttonsMarginBottom;

          // Also check if buttons container is inside a col that might have gap
          const colElement = buttonsContainer.closest('.col');
          if(colElement){
            const colStyle = getComputedStyle(colElement);
            const colGap = parseInt(colStyle.gap) || 0;
            // Add gap if buttons container is not the first child
            if(buttonsContainer.previousElementSibling){
              buttonsHeight += colGap;
            }
          }
        }
      }

      requiredPanelH = contentHeight + buttonsHeight + (panelPadding * 2) + (panelMargin * 2) + 4; // Add padding, margin, and small buffer

      panelEl.style.height = originalHeight;
      panelEl.style.overflow = originalOverflow;
      panelEl.style.maxHeight = originalMaxHeight;
    }

    // Calculate maximum available panel height based on screen constraints
    const minCanvasHeight = 120; // Minimum canvas height
    const isMobile = window.innerWidth <= 860;
    const availableSpace = vh - topbar - reservedMargins;

    // Dynamic height ratio based on viewport height
    let canvasRatio, panelRatio;
    if(isMobile) {
      // Mobile: adjust based on viewport height
      if(vh < 600) {
        // Very small screens: prioritize panel content visibility
        canvasRatio = 0.35;
        panelRatio = 0.65;
      } else if(vh < 800) {
        // Small screens: balanced
        canvasRatio = 0.40;
        panelRatio = 0.60;
      } else if(vh < 1000) {
        // Medium mobile screens: more balanced
        canvasRatio = 0.45;
        panelRatio = 0.55;
      } else {
        // Large mobile screens: more canvas space
        canvasRatio = 0.50;
        panelRatio = 0.50;
      }
    } else {
      // Desktop: adjust based on viewport height
      if(vh < 700) {
        // Small desktop: balanced
        canvasRatio = 0.50;
        panelRatio = 0.50;
      } else if(vh < 900) {
        // Medium desktop: more canvas
        canvasRatio = 0.55;
        panelRatio = 0.45;
      } else if(vh < 1200) {
        // Large desktop: prioritize canvas
        canvasRatio = 0.60;
        panelRatio = 0.40;
      } else {
        // Very large desktop: maximize canvas
        canvasRatio = 0.65;
        panelRatio = 0.35;
      }
    }

    // Calculate panel height - prioritize ensuring all panel content is visible
    const maxPanelHeight = Math.floor(availableSpace * panelRatio);

    // Calculate maximum panel height that still allows canvas minimum
    let maxPanelForCanvas = availableSpace - minCanvasHeight - reservedMargins;

    // If required panel height exceeds available space with canvas minimum,
    // reduce canvas minimum to ensure panel content fits
    if(requiredPanelH > maxPanelForCanvas && requiredPanelH <= availableSpace - reservedMargins) {
      // Panel content needs more space, reduce canvas minimum
      maxPanelForCanvas = availableSpace - reservedMargins;
    }

    let computedPanelH;

    // Prioritize showing all panel content including buttons
    if(requiredPanelH > PANEL_H_MIN) {
      // If content fits within constraints, use content height
      if(requiredPanelH <= maxPanelHeight && requiredPanelH <= panelMaxPx && requiredPanelH <= maxPanelForCanvas) {
        computedPanelH = requiredPanelH; // Content fits, use content height
      } else {
        // Content doesn't fit in ratio-based space, prioritize panel content visibility
        // If required height exceeds available space with canvas minimum, reduce canvas
        if(requiredPanelH > maxPanelForCanvas && requiredPanelH <= availableSpace - reservedMargins) {
          // Panel content needs more space, use required height (will reduce canvas)
          computedPanelH = Math.min(requiredPanelH, panelMaxPx, availableSpace - reservedMargins);
        } else {
          // Use maximum available space while maintaining canvas minimum
          computedPanelH = Math.max(PANEL_H_MIN, Math.min(panelMaxPx, maxPanelForCanvas, maxPanelHeight));
        }
      }
    } else {
      computedPanelH = Math.max(PANEL_H_MIN, Math.min(panelMaxPx, maxPanelHeight, maxPanelForCanvas));
    }

    if(computedPanelH < PANEL_H_MIN) computedPanelH = PANEL_H_MIN;

    // Final check: ensure panel doesn't exceed available space
    if(computedPanelH > availableSpace - reservedMargins) {
      computedPanelH = Math.max(PANEL_H_MIN, availableSpace - reservedMargins);
    }

    if(panelEl) panelEl.style.height = computedPanelH + 'px';

    // Calculate canvas available height - maximize canvas while ensuring panel content fits
    // Strategy: Use all remaining space after panel takes its required space
    const remainingSpace = availableSpace - computedPanelH - reservedMargins;

    let canvasAvail;

    if(isMobile) {
      // On mobile: maximize canvas while ensuring panel content is visible
      const mobileMinCanvasHeight = 60; // Minimum canvas height for mobile

      // Calculate maximum canvas height based on viewport
      // Use a higher ratio to maximize canvas size
      const maxCanvasHeightRatio = 0.50; // Maximum 50% of viewport height on mobile
      const absoluteMaxCanvas = Math.floor(vh * maxCanvasHeightRatio);

      // Use all remaining space after panel, but respect maximum ratio
      canvasAvail = Math.max(mobileMinCanvasHeight, Math.min(remainingSpace, absoluteMaxCanvas));

      // Final check: ensure panel buttons are visible
      const panelWithButtons = computedPanelH + reservedMargins;
      const totalUsed = panelWithButtons + canvasAvail;
      if(totalUsed > availableSpace) {
        // Reduce canvas only if absolutely necessary to fit panel
        canvasAvail = Math.max(mobileMinCanvasHeight, availableSpace - panelWithButtons);
      }
    } else {
      // Desktop: maximize canvas height - use most of the viewport
      const maxCanvasHeightRatio = 0.70; // Maximum 70% of viewport height on desktop
      const maxCanvasHeight = Math.floor(vh * maxCanvasHeightRatio);

      // Use all remaining space after panel, up to the maximum ratio
      canvasAvail = Math.max(minCanvasHeight, Math.min(remainingSpace, maxCanvasHeight));

      // Ensure panel content fits - if panel needs more space, reduce canvas accordingly
      if(requiredPanelH > PANEL_H_MIN) {
        const canvasForPanel = availableSpace - requiredPanelH - reservedMargins;
        if(canvasForPanel < canvasAvail) {
          // Only reduce if panel actually needs the space
          canvasAvail = Math.max(minCanvasHeight, canvasForPanel);
        }
      }
    }

    canvasAvail = Math.max(isMobile ? 60 : minCanvasHeight, Math.floor(canvasAvail));
    if(canvasWrap) {
      // Clear any cached styles and set height with !important to prevent cache interference
      canvasWrap.style.removeProperty('height');
      canvasWrap.style.removeProperty('max-height');
      canvasWrap.style.removeProperty('min-height');

      // Set height and max-height using setProperty with !important to ensure cache doesn't override
      canvasWrap.style.setProperty('height', canvasAvail + 'px', 'important');
      canvasWrap.style.setProperty('max-height', canvasAvail + 'px', 'important');
      canvasWrap.style.setProperty('min-height', 'auto', 'important');
      canvasWrap.style.setProperty('flex-shrink', '0', 'important');
      canvasWrap.style.setProperty('flex-grow', '0', 'important');

      // On mobile, ensure canvas-wrap doesn't overlap with topbar
      if(isMobile) {
        canvasWrap.style.setProperty('margin-top', '0', 'important');
        canvasWrap.style.setProperty('padding-top', '0', 'important');
        canvasWrap.style.setProperty('position', 'relative', 'important');
      }
    }

    const canvasContainerRect = canvasWrap.getBoundingClientRect();
    const availW = Math.max(200, Math.floor(canvasContainerRect.width));
    const availH = Math.max(120, Math.floor(canvasContainerRect.height));
    let targetAspect = camera.aspect || (16/9);

    let useW = availW; let useH = Math.round(useW / targetAspect);
    if(isMobile){
      // On mobile, make canvas nearly the same size as wrapper (centered)
      useW = availW; useH = availH; targetAspect = useW / useH;
    } else {
      // Maximize canvas size while maintaining aspect ratio
      if(useH > availH){ useH = availH; useW = Math.round(useH * targetAspect); }
      // If width is still within bounds, use full available width
      if(useW <= availW && useH <= availH){
        useW = availW;
        useH = Math.round(useW / targetAspect);
        if(useH > availH){ useH = availH; useW = Math.round(useH * targetAspect); }
      }
    }
    useW = Math.max(200, Math.min(useW, availW)); useH = Math.max(120, Math.min(useH, availH));

    const canvasEl = renderer.domElement;
    canvasEl.style.width = useW + 'px'; canvasEl.style.height = useH + 'px';
    const devicePR = Math.min(DPR, window.devicePixelRatio || 1);
    renderer.setPixelRatio(devicePR); renderer.setSize(useW, useH, false);
    try{ canvasEl.width = Math.floor(useW * devicePR); canvasEl.height = Math.floor(useH * devicePR); }catch(e){}
    camera.aspect = useW / useH; camera.updateProjectionMatrix();
    try{ controls.update(); renderer.render(scene, camera); }catch(e){}
  }catch(err){ safeLog('resizeCanvasToAvailable error', err); }
}

function adjustGuideTextFontSize(){
  try{
    const guideText = document.getElementById('guideText');
    if(!guideText) return;
    const parent = guideText.parentElement;
    if(!parent) return;

    // 初期フォントサイズを設定（デスクトップ/モバイルに応じて）
    const isMobile = window.innerWidth <= 860;
    const maxFontSize = isMobile ? 1.1 : 1.2;
    const minFontSize = isMobile ? 11 : 12;

    // 一時的に最大フォントサイズを設定して測定
    guideText.style.fontSize = maxFontSize + 'em';
    const parentWidth = parent.clientWidth;
    const textWidth = guideText.scrollWidth;

    // テキストが親要素の幅を超える場合、フォントサイズを縮小
    if(textWidth > parentWidth){
      const ratio = parentWidth / textWidth;
      const newFontSize = Math.max(minFontSize, Math.floor(maxFontSize * ratio * 16)); // emをpxに変換（16px基準）
      guideText.style.fontSize = newFontSize + 'px';
    } else {
      // 収まる場合は最大フォントサイズを使用
      guideText.style.fontSize = maxFontSize + 'em';
    }
  }catch(e){ safeLog('adjustGuideTextFontSize', e); }
}

window.addEventListener('resize', () => {
  setTimeout(() => {
    resizeCanvasToAvailable();
    adjustGuideTextFontSize();
  }, 80);
});
window.addEventListener('orientationchange', () => {
  setTimeout(() => {
    resizeCanvasToAvailable();
    adjustGuideTextFontSize();
  }, 200);
});

(function initDrag(){
  try{
    let dragging=false, startY=0, startHeight=0;
    const panelHandle = document.getElementById('panelHandle');
    panelHandle.addEventListener('pointerdown', (ev)=>{
      ev.preventDefault(); dragging = true; startY = ev.clientY;
      startHeight = parseFloat(getComputedStyle(document.getElementById('panel')).height) || startHeight;
      panelHandle.setPointerCapture?.(ev.pointerId);
      document.body.style.userSelect = 'none';
    });
    window.addEventListener('pointermove', (ev)=>{
      if(!dragging) return;
      ev.preventDefault();
      const delta = startY - ev.clientY;
      let newHeight = startHeight + delta;
      const vh = window.innerHeight;
      const panelMaxPx = getCssPanelMaxPx(vh);
      newHeight = Math.max(PANEL_H_MIN, Math.min(panelMaxPx, newHeight));
      const panelEl = document.getElementById('panel');
      if(panelEl) panelEl.style.height = newHeight + 'px';
      resizeCanvasToAvailable();
    });
    window.addEventListener('pointerup', (ev)=>{
      if(!dragging) return;
      dragging = false;
      try{ panelHandle.releasePointerCapture?.(ev ? ev.pointerId : undefined); }catch(e){}
      document.body.style.userSelect = '';
      resizeCanvasToAvailable();
    });
  }catch(e){ safeLog('initDrag error', e); }
})();

(function setupWakeAndRender(){
  try{
    let woke = false;
    function wake(){ if(woke) return; woke = true; try{ controls.update(); renderer.render(scene, camera); }catch(e){} document.removeEventListener('pointerdown', wake); document.removeEventListener('touchstart', wake); }
    document.addEventListener('pointerdown', wake, { passive:true });
    document.addEventListener('touchstart', wake, { passive:true });
  }catch(e){}
  (function animate(){ requestAnimationFrame(animate); try{ controls.update(); renderer.render(scene, camera); }catch(e){} })();
})();

modelSelect && modelSelect.addEventListener('change', () => {
  try {
    const url = modelSelect.value;
    if(!url){
      loadModel('').catch(()=>{ setStatus('モデル未選択', true); });
      return;
    }
    try{ localStorage.setItem(STORAGE_KEYS.selectedModelUrl, url); }catch(e){ safeLog('persist model failed', e); }
    loadModel(url).catch(err=>{ safeLog('loadModel rejected', err); setStatus('モデル読み込み失敗', true); });
  } catch (e) { safeLog('modelSelect change error', e); }
});

reloadModels && reloadModels.addEventListener('click', () => loadModelsJson().then(()=>{
  resizeCanvasToAvailable();
  const saved = localStorage.getItem(STORAGE_KEYS.selectedModelUrl);
  if(saved){ const opt = Array.from(modelSelect.options).find(o=>o.value===saved); if(opt) modelSelect.value = saved; }
  if(modelSelect.options.length>1 && modelSelect.value) loadModel(modelSelect.value);
}));

async function loadModelsJson(){
  setStatus('models.json 読み込み中...');
  try{
    const res = await fetch(MODELS_JSON_PATH, { cache: 'no-store' });
    if(!res.ok) throw new Error(`${MODELS_JSON_PATH} が見つかりません (${res.status})`);
    const j = await res.json();
    if(!Array.isArray(j)) throw new Error('models.json は配列である必要があります');
    modelsJson = j;
    populateModelSelect();
    setStatus('models.json 読み込み完了');
    return j;
  }catch(err){
    safeLog('loadModelsJson failed', err);
    setStatus('models.json 読み込み失敗', true);
    if(modelSelect) modelSelect.innerHTML = '<option>読み込み失敗</option>';
    return [];
  }
}

(async ()=>{
  try{
    initThree();
    await loadModelsJson();
    const savedModel = localStorage.getItem(STORAGE_KEYS.selectedModelUrl);
    if(savedModel){
      const opt = Array.from(modelSelect.options).find(o=>o.value===savedModel);
      if(opt){ modelSelect.value = savedModel; await loadModel(savedModel); }
    } else {
      if(modelSelect.options.length > 1){
        modelSelect.selectedIndex = 1;
        const url = modelSelect.value;
        if(url) await loadModel(url);
      }
    }
    applyBtn && applyBtn.classList.toggle('active', liveApply);
    if(applyBtn) applyBtn.textContent = liveApply ? 'ライブ適用中' : '適用';
    resizeCanvasToAvailable(); setTimeout(resizeCanvasToAvailable, 160);
    adjustGuideTextFontSize();
    setTimeout(adjustGuideTextFontSize, 200);
    setStatus('準備完了');
  }catch(e){ safeLog('initial boot error', e); setStatus('初期化エラー', true); }
})();

window._app = { renderer, scene, camera, controls, loadModel, resizeCanvasToAvailable, modelsJson, meshMap, originalMaterials, clonedMaterials };
