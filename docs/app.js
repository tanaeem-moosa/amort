/**
 * Verified Algorithms Skill Tree — Core Application Engine
 * Pure ES6+ Static Client-Side Application
 * Zero external dependencies. Ready for GitHub Pages and offline file:// execution.
 */

// ==============================================================================
// 1. Canonical Layout & Constants
// ==============================================================================

const STORAGE_KEYS = ['amort_skill_tree_save_v1', 'amort_skill_tree_progress_v1'];

function escapeHTML(str) {
  if (str === null || str === undefined) return '';
  return String(str)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#039;');
}
if (typeof window !== 'undefined') {
  window.escapeHTML = escapeHTML;
}

const NODE_WIDTH = 216;
const NODE_HEIGHT = 96;

/**
 * Hand-tuned, symmetric, 5-lane coordinates across 6 tiers.
 * Guarantees zero overlaps and optimal downward bezier wire flow.
 */
const LANE_COORDINATES = {
  // Tier 1: Root
  BGCD:   { x: 1350, y: 80 },

  // Tier 2: Arithmetic, Sorting, Amortization
  EUC:    { x: 220,  y: 280 },
  MODEXP: { x: 480,  y: 280 },
  INS:    { x: 780,  y: 280 },
  BS:     { x: 1040, y: 280 },
  DYN:    { x: 1750, y: 280 },

  // Tier 3: Fan-ins and data structures
  EXT:    { x: 220,  y: 480 },
  MERGE:  { x: 910,  y: 480 },
  NAIVE:  { x: 1260, y: 480 },
  TSQ:    { x: 1620, y: 480 },
  HEAP:   { x: 1880, y: 480 },

  // Tier 4: Core algorithms
  LB:     { x: 650,  y: 680 },
  QS:     { x: 890,  y: 680 },
  INTV:   { x: 1130, y: 680 },
  LCS:    { x: 1370, y: 680 },
  KMP:    { x: 1600, y: 680 },
  BFS:    { x: 1860, y: 680 },
  DIJ:    { x: 2120, y: 680 },

  // Tier 5: Advanced & Reductions
  RED:    { x: 650,  y: 880 },
  ED:     { x: 1250, y: 880 },
  KNAP:   { x: 1490, y: 880 },
  Z:      { x: 1710, y: 880 },
  AC:     { x: 1930, y: 880 },
  BF:     { x: 2150, y: 880 },
  TWOSAT: { x: 2370, y: 880 },
  DSU:    { x: 2590, y: 880 },

  // Tier 6: Sinks
  LIS:    { x: 1490, y: 1080 },
  KRUS:   { x: 2590, y: 1080 }
};

// ==============================================================================
// 2. Skill Tree Engine (State & Dependency Machine)
// ==============================================================================

class SkillTreeEngine {
  constructor(treeData) {
    this.treeData = treeData;
    this.nodes = treeData.nodes || [];
    this.categories = new Map((treeData.categories || []).map(c => [c.id, c]));
    this.nodesMap = new Map(this.nodes.map(n => [n.id, n]));

    this.masteredNodes = new Set();
    this.answers = {};

    this.loadState();
  }

  loadState() {
    for (const key of STORAGE_KEYS) {
      try {
        const raw = localStorage.getItem(key);
        if (raw) {
          const parsed = JSON.parse(raw);
          if (Array.isArray(parsed.mastered_nodes)) {
            this.masteredNodes = new Set(parsed.mastered_nodes.filter(id => this.nodesMap.has(id)));
          }
          if (parsed.answers && typeof parsed.answers === 'object') {
            this.answers = parsed.answers;
          }
          return;
        }
      } catch (e) {
        console.warn('Could not read from storage key', key, e);
      }
    }
  }

  saveState() {
    const payload = {
      schema_version: '1.0.0',
      saved_at: new Date().toISOString(),
      mastered_nodes: Array.from(this.masteredNodes).sort(),
      answers: this.answers
    };
    const jsonStr = JSON.stringify(payload);
    for (const key of STORAGE_KEYS) {
      try {
        localStorage.setItem(key, jsonStr);
      } catch (e) {
        console.warn('Could not write to storage key', key, e);
      }
    }
  }

  computeNodeStates() {
    const states = {};
    for (const node of this.nodes) {
      if (node.status === 'planned') {
        states[node.id] = 'planned';
      } else if (this.masteredNodes.has(node.id)) {
        states[node.id] = 'mastered';
      } else {
        const prereqs = node.prerequisites || [];
        const allSatisfied = prereqs.every(p => this.masteredNodes.has(p));
        states[node.id] = (prereqs.length === 0 || allSatisfied) ? 'active' : 'locked';
      }
    }
    return states;
  }

  markNodeMastered(nodeId) {
    const node = this.nodesMap.get(nodeId);
    if (!node || node.status === 'planned') {
      return false;
    }
    const prereqs = node.prerequisites || [];
    if (prereqs.length > 0 && !prereqs.every(p => this.masteredNodes.has(p))) {
      console.warn(`Cannot master locked node '${nodeId}': unsatisfied prerequisites [${prereqs.filter(p => !this.masteredNodes.has(p)).join(', ')}]`);
      return false;
    }
    if (!this.masteredNodes.has(nodeId)) {
      this.masteredNodes.add(nodeId);
      this.saveState();
      return true; // Newly unlocked transition
    }
    return false;
  }

  recordAnswer(nodeId, quizType, questionId, answer) {
    if (!this.answers[nodeId] || typeof this.answers[nodeId] !== 'object' || Array.isArray(this.answers[nodeId])) {
      this.answers[nodeId] = { predict: {}, spot_the_fake: {} };
    }
    if (!this.answers[nodeId][quizType] || typeof this.answers[nodeId][quizType] !== 'object' || Array.isArray(this.answers[nodeId][quizType])) {
      this.answers[nodeId][quizType] = {};
    }
    this.answers[nodeId][quizType][questionId] = String(answer).trim();
    this.saveState();
  }

  getRecordedAnswer(nodeId, quizType, questionId) {
    return this.answers[nodeId]?.[quizType]?.[questionId] || null;
  }

  isNodeCompleted(nodeId) {
    if (this.masteredNodes.has(nodeId)) return true;
    const node = this.nodesMap.get(nodeId);
    if (!node || !node.exercises) return false;

    const predicts = node.exercises.predict || [];
    const fakes = node.exercises.spot_the_fake || [];
    if (predicts.length === 0 && fakes.length === 0) return false;

    const nodeAns = this.answers[nodeId] || { predict: {}, spot_the_fake: {} };

    // Check predict answers
    for (const p of predicts) {
      const userAns = nodeAns.predict?.[p.id];
      if (!userAns || userAns.toLowerCase() !== String(p.expected_answer).trim().toLowerCase()) {
        return false;
      }
    }

    // Check spot the fake answers
    for (const f of fakes) {
      const userAns = nodeAns.spot_the_fake?.[f.id];
      const correctId = f.correct_option_id || f.options?.find(o => !o.is_fake)?.id;
      if (!userAns || userAns.toLowerCase() !== String(correctId).trim().toLowerCase()) {
        return false;
      }
    }

    return true;
  }

  exportSavefile() {
    return {
      schema_version: '1.0.0',
      saved_at: new Date().toISOString(),
      mastered_nodes: Array.from(this.masteredNodes).sort(),
      answers: JSON.parse(JSON.stringify(this.answers))
    };
  }

  importSavefile(payload) {
    if (typeof payload === 'string') {
      try {
        payload = JSON.parse(payload);
      } catch (e) {
        throw new ValueError(`Invalid JSON string: ${e.message}`);
      }
    }
    if (!payload || typeof payload !== 'object' || Array.isArray(payload)) {
      throw new ValueError('Savefile payload must be a JSON object');
    }
    if (payload.schema_version !== '1.0.0') {
      throw new ValueError(`Unsupported schema version: ${payload.schema_version}`);
    }
    if (!Array.isArray(payload.mastered_nodes)) {
      throw new ValueError("'mastered_nodes' must be a list");
    }

    const masteredSet = new Set();
    for (const nid of payload.mastered_nodes) {
      if (typeof nid !== 'string' || !nid) {
        throw new ValueError(`Invalid node ID in mastered_nodes: ${JSON.stringify(nid)}`);
      }
      if (!this.nodesMap.has(nid)) {
        throw new ValueError(`Savefile references unknown node ID: ${nid}`);
      }
      if (this.nodesMap.get(nid).status === 'planned') {
        throw new ValueError(`Savefile illegally claims planned node '${nid}' as mastered`);
      }
      masteredSet.add(nid);
    }

    // Validate prerequisite topological closure
    for (const nid of masteredSet) {
      const node = this.nodesMap.get(nid);
      for (const p of (node.prerequisites || [])) {
        if (!masteredSet.has(p)) {
          throw new ValueError(`Savefile topological closure violation: Node '${nid}' is marked mastered, but prerequisite '${p}' is not in mastered_nodes`);
        }
      }
    }

    // Validate answers dictionary
    if (payload.answers !== undefined) {
      if (typeof payload.answers !== 'object' || payload.answers === null || Array.isArray(payload.answers)) {
        throw new ValueError("'answers' must be a JSON dictionary");
      }
      for (const [nid, ansObj] of Object.entries(payload.answers)) {
        if (typeof ansObj !== 'object' || ansObj === null || Array.isArray(ansObj)) {
          throw new ValueError(`'answers.${nid}' must be a JSON dictionary`);
        }
        for (const [qType, qVal] of Object.entries(ansObj)) {
          if (typeof qVal !== 'object' || qVal === null || Array.isArray(qVal)) {
            throw new ValueError(`'answers.${nid}.${qType}' must be a JSON dictionary`);
          }
        }
      }
    }

    this.masteredNodes = masteredSet;
    this.answers = JSON.parse(JSON.stringify(payload.answers || {}));
    this.saveState();
    return this.computeNodeStates();
  }

  resetProgress() {
    this.masteredNodes.clear();
    this.answers = {};
    for (const key of STORAGE_KEYS) {
      try {
        localStorage.removeItem(key);
      } catch (e) {
        // ignore
      }
    }
    this.saveState();
    return this.computeNodeStates();
  }
}

class ValueError extends Error {
  constructor(message) {
    super(message);
    this.name = 'ValueError';
  }
}

// ==============================================================================
// 3. Application UI & Canvas Controller
// ==============================================================================

class SkillTreeApp {
  constructor() {
    this.engine = null;
    this.nodeStates = {};
    this.selectedNodeId = null;

    // Viewport transform
    this.panX = 100;
    this.panY = 60;
    this.scale = 0.85;
    this.minScale = 0.25;
    this.maxScale = 3.0;

    // Drag state
    this.isDragging = false;
    this.dragStartX = 0;
    this.dragStartY = 0;
    this.dragStartPanX = 0;
    this.dragStartPanY = 0;

    // DOM references
    this.viewportEl = document.getElementById('canvas-container');
    this.worldEl = document.getElementById('canvas-world');
    this.wiresLayerEl = document.getElementById('wires-layer');
    this.nodesLayerEl = document.getElementById('nodes-layer');
    this.drawerEl = document.getElementById('inspector-drawer');
    this.dropOverlayEl = document.getElementById('drop-overlay');
    this.resetModalEl = document.getElementById('confirm-reset-dialog');

    this.statMasteredEl = document.getElementById('stat-mastered');
    this.statProgressFillEl = document.getElementById('stat-progress-fill');

    this.readingViewEl = document.getElementById('reading-view');
    this.readingArticleEl = document.getElementById('reading-article');
    this.readingBackLinkEl = document.getElementById('reading-back-link');
    this.drawerOpenChapterBtnEl = document.getElementById('drawer-open-chapter-btn');
  }

  async init() {
    const treeData = await this.loadTreeData();
    this.engine = new SkillTreeEngine(treeData);
    this.nodeStates = this.engine.computeNodeStates();

    this.setupEventListeners();
    this.setupPanAndZoom();
    this.setupSavefileHandlers();
    this.setupDrawer();

    this.render();
    this.updateHUD();
    this.centerOnRoot();

    this.setupRouting();
  }

  // ----------------------------------------------------------------------------
  // Triple-Tier Data Loading
  // ----------------------------------------------------------------------------
  async loadTreeData() {
    // 1. Dynamic fetch attempt
    const paths = ['tutorial/tree.json', '../tutorial/tree.json', 'tree.json'];
    for (const path of paths) {
      try {
        const res = await fetch(path);
        if (res.ok) {
          const json = await res.json();
          if (json && Array.isArray(json.nodes) && json.nodes.length >= 20) {
            return json;
          }
        }
      } catch (err) {
        // Fall through to next tier
      }
    }

    // 2. Secondary fallback: window.__TREE_DATA_FALLBACK__ from tree_data.js
    if (window.__TREE_DATA_FALLBACK__ && Array.isArray(window.__TREE_DATA_FALLBACK__.nodes)) {
      return window.__TREE_DATA_FALLBACK__;
    }

    // 3. Tertiary fallback: embedded script
    const embedded = document.getElementById('tree-data-embedded');
    if (embedded && embedded.textContent) {
      try {
        const parsed = JSON.parse(embedded.textContent);
        if (parsed && Array.isArray(parsed.nodes)) return parsed;
      } catch (e) {
        // ignore
      }
    }

    throw new Error('Failed to load skill tree data across all 3 tiers.');
  }

  // ----------------------------------------------------------------------------
  // Node Positioning Logic
  // ----------------------------------------------------------------------------
  getNodeCoordinates(nodeId) {
    if (LANE_COORDINATES[nodeId]) {
      return LANE_COORDINATES[nodeId];
    }
    // Dynamic automated fallback layout based on tier and index
    const node = this.engine.nodesMap.get(nodeId);
    const tier = node?.tier || 1;
    const sameTierNodes = this.engine.nodes.filter(n => n.tier === tier);
    const index = sameTierNodes.findIndex(n => n.id === nodeId);
    const count = sameTierNodes.length;
    const spacing = 260;
    const startX = 1400 - ((count - 1) * spacing) / 2;
    return {
      x: startX + index * spacing,
      y: 80 + (tier - 1) * 200
    };
  }

  // ----------------------------------------------------------------------------
  // Canvas Rendering (Nodes & Glowing SVG Wires)
  // ----------------------------------------------------------------------------
  render() {
    this.renderWires();
    this.renderNodes();
    this.updateTransform();
  }

  renderNodes() {
    this.nodesLayerEl.innerHTML = '';

    for (const node of this.engine.nodes) {
      const pos = this.getNodeCoordinates(node.id);
      const state = this.nodeStates[node.id] || 'locked';
      const category = this.engine.categories.get(node.category);
      const catColor = category?.color || '#38bdf8';

      const card = document.createElement('div');
      card.className = `tree-node state-${state}`;
      if (this.selectedNodeId === node.id) {
        card.classList.add('is-selected');
      }
      card.id = `node-${node.id}`;
      card.dataset.nodeId = node.id;
      card.style.left = `${pos.x}px`;
      card.style.top = `${pos.y}px`;
      card.tabIndex = 0;

      // Status indicator icon
      let statusIcon = '🔒';
      if (state === 'mastered') statusIcon = '✓';
      else if (state === 'active') statusIcon = '⚡';
      else if (state === 'planned') statusIcon = '✎';

      const quizCount = (node.exercises?.predict?.length || 0) + (node.exercises?.spot_the_fake?.length || 0);

      card.innerHTML = `
        <div class="node-top">
          <span class="node-badge-category" style="color: ${catColor}; border-left: 3px solid ${catColor};">
            ${category?.name ? category.name.split(' ')[0] : node.category}
          </span>
          <span class="node-id">${node.id}</span>
          <span class="node-status-icon">${statusIcon}</span>
        </div>
        <div class="node-title" title="${node.name}">${node.name}</div>
        <div class="node-bottom">
          <span class="node-tier-tag">T${node.tier}</span>
          <span class="node-quiz-count">${quizCount ? `${quizCount} quiz${quizCount > 1 ? 'zes' : ''}` : 'Reference'}</span>
        </div>
      `;

      card.addEventListener('click', (e) => {
        e.stopPropagation();
        this.selectNode(node.id);
      });

      card.addEventListener('keydown', (e) => {
        if (e.key === 'Enter' || e.key === ' ') {
          e.preventDefault();
          this.selectNode(node.id);
        }
      });

      this.nodesLayerEl.appendChild(card);
    }
  }

  renderWires() {
    this.wiresLayerEl.innerHTML = '';

    for (const node of this.engine.nodes) {
      const parentPos = this.getNodeCoordinates(node.id);
      const parentBottomX = parentPos.x + NODE_WIDTH / 2;
      const parentBottomY = parentPos.y + NODE_HEIGHT;
      const parentState = this.nodeStates[node.id] || 'locked';

      for (const childId of (node.unlocks || [])) {
        const childPos = this.getNodeCoordinates(childId);
        const childTopX = childPos.x + NODE_WIDTH / 2;
        const childTopY = childPos.y;
        const childState = this.nodeStates[childId] || 'locked';

        // Determine wire state
        let wireState = 'locked';
        if (childState === 'planned' || parentState === 'planned') {
          wireState = 'planned';
        } else if (parentState === 'mastered') {
          wireState = (childState === 'mastered') ? 'mastered' : 'active';
        }

        // SVG Cubic Bezier routing
        const deltaY = childTopY - parentBottomY;
        const controlY1 = parentBottomY + Math.max(deltaY * 0.45, 40);
        const controlY2 = childTopY - Math.max(deltaY * 0.45, 40);

        const d = `M ${parentBottomX} ${parentBottomY} C ${parentBottomX} ${controlY1}, ${childTopX} ${controlY2}, ${childTopX} ${childTopY}`;

        const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
        path.setAttribute('d', d);
        path.setAttribute('class', `tree-wire wire-${wireState}`);
        path.setAttribute('marker-end', `url(#marker-${wireState})`);
        this.wiresLayerEl.appendChild(path);
      }
    }
  }

  // ----------------------------------------------------------------------------
  // Pan & Zoom Engine
  // ----------------------------------------------------------------------------
  setupPanAndZoom() {
    const vp = this.viewportEl;

    // Pointer Events Drag Pan
    vp.addEventListener('pointerdown', (e) => {
      if (e.target.closest('.tree-node') || e.target.closest('.canvas-controls')) return;
      this.isDragging = true;
      this.dragStartX = e.clientX;
      this.dragStartY = e.clientY;
      this.dragStartPanX = this.panX;
      this.dragStartPanY = this.panY;
      vp.classList.add('is-dragging');
      vp.setPointerCapture(e.pointerId);
    });

    vp.addEventListener('pointermove', (e) => {
      if (!this.isDragging) return;
      const dx = e.clientX - this.dragStartX;
      const dy = e.clientY - this.dragStartY;
      this.panX = this.dragStartPanX + dx;
      this.panY = this.dragStartPanY + dy;
      this.updateTransform();
    });

    const stopDrag = (e) => {
      if (this.isDragging) {
        this.isDragging = false;
        vp.classList.remove('is-dragging');
        try {
          vp.releasePointerCapture(e.pointerId);
        } catch (err) {
          // ignore
        }
      }
    };

    vp.addEventListener('pointerup', stopDrag);
    vp.addEventListener('pointercancel', stopDrag);

    // Cursor-anchored Wheel Zoom
    vp.addEventListener('wheel', (e) => {
      e.preventDefault();
      const rect = vp.getBoundingClientRect();
      const cursorX = e.clientX - rect.left;
      const cursorY = e.clientY - rect.top;

      const zoomFactor = e.deltaY < 0 ? 1.15 : 0.87;
      this.zoomAtPoint(cursorX, cursorY, zoomFactor);
    }, { passive: false });

    // Floating Zoom Controls
    document.getElementById('btn-zoom-in')?.addEventListener('click', () => {
      const rect = vp.getBoundingClientRect();
      this.zoomAtPoint(rect.width / 2, rect.height / 2, 1.25);
    });

    document.getElementById('btn-zoom-out')?.addEventListener('click', () => {
      const rect = vp.getBoundingClientRect();
      this.zoomAtPoint(rect.width / 2, rect.height / 2, 0.8);
    });

    document.getElementById('btn-zoom-fit')?.addEventListener('click', () => {
      this.fitTreeToView();
    });

    document.getElementById('btn-zoom-root')?.addEventListener('click', () => {
      this.centerOnRoot();
    });
  }

  zoomAtPoint(clientX, clientY, factor) {
    const newScale = Math.max(this.minScale, Math.min(this.scale * factor, this.maxScale));
    if (newScale === this.scale) return;

    // Anchor equation
    this.panX = clientX - (clientX - this.panX) * (newScale / this.scale);
    this.panY = clientY - (clientY - this.panY) * (newScale / this.scale);
    this.scale = newScale;

    this.updateTransform();
  }

  updateTransform() {
    this.worldEl.style.transform = `translate(${this.panX}px, ${this.panY}px) scale(${this.scale})`;
  }

  centerOnRoot() {
    const rootPos = this.getNodeCoordinates('BGCD');
    const rect = this.viewportEl.getBoundingClientRect();
    this.scale = 0.9;
    this.panX = rect.width / 2 - (rootPos.x + NODE_WIDTH / 2) * this.scale;
    this.panY = 40;
    this.updateTransform();
  }

  fitTreeToView() {
    let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
    for (const node of this.engine.nodes) {
      const pos = this.getNodeCoordinates(node.id);
      minX = Math.min(minX, pos.x);
      maxX = Math.max(maxX, pos.x + NODE_WIDTH);
      minY = Math.min(minY, pos.y);
      maxY = Math.max(maxY, pos.y + NODE_HEIGHT);
    }

    const padding = 60;
    const treeW = maxX - minX + padding * 2;
    const treeH = maxY - minY + padding * 2;

    const vpRect = this.viewportEl.getBoundingClientRect();
    const scaleX = vpRect.width / treeW;
    const scaleY = vpRect.height / treeH;
    this.scale = Math.max(this.minScale, Math.min(Math.min(scaleX, scaleY), 1.0));

    this.panX = (vpRect.width - treeW * this.scale) / 2 - (minX - padding) * this.scale;
    this.panY = (vpRect.height - treeH * this.scale) / 2 - (minY - padding) * this.scale;

    this.updateTransform();
  }

  // ----------------------------------------------------------------------------
  // HUD Status Display
  // ----------------------------------------------------------------------------
  updateHUD() {
    const readyOrOpenNodes = this.engine.nodes.filter(n => n.status !== 'planned');
    const totalReady = readyOrOpenNodes.length; // 22 canonical ready/open
    const masteredCount = this.engine.masteredNodes.size;

    if (this.statMasteredEl) {
      this.statMasteredEl.textContent = `${masteredCount} / ${totalReady}`;
    }

    if (this.statProgressFillEl) {
      const pct = totalReady > 0 ? (masteredCount / totalReady) * 100 : 0;
      this.statProgressFillEl.style.width = `${Math.min(100, pct)}%`;
      this.statProgressFillEl.parentElement?.setAttribute('aria-valuenow', masteredCount);
    }
  }

  // ----------------------------------------------------------------------------
  // Inspector Drawer Controller
  // ----------------------------------------------------------------------------
  setupDrawer() {
    const drawer = this.drawerEl;
    if (!drawer) return;

    // Close button
    document.getElementById('btn-drawer-close')?.addEventListener('click', () => {
      this.closeDrawer();
    });

    // Light dismiss: click on dialog backdrop closes it
    drawer.addEventListener('click', (e) => {
      const rect = drawer.getBoundingClientRect();
      const isInDialog = (
        rect.top <= e.clientY && e.clientY <= rect.bottom &&
        rect.left <= e.clientX && e.clientX <= rect.right
      );
      if (!isInDialog) {
        this.closeDrawer();
      }
    });

    // Tab navigation
    const tabs = drawer.querySelectorAll('.tab-btn');
    tabs.forEach(btn => {
      btn.addEventListener('click', () => {
        const targetTab = btn.dataset.tab;
        this.switchDrawerTab(targetTab);
      });
    });
  }

  switchDrawerTab(tabId) {
    const drawer = this.drawerEl;
    drawer.querySelectorAll('.tab-btn').forEach(btn => {
      const isActive = (btn.dataset.tab === tabId);
      btn.classList.toggle('active', isActive);
      btn.setAttribute('aria-selected', isActive ? 'true' : 'false');
    });

    drawer.querySelectorAll('.tab-content').forEach(panel => {
      panel.classList.toggle('active', panel.id === `tab-${tabId}`);
    });
  }

  setupRouting() {
    window.addEventListener('hashchange', () => this.handleRouting());
    this.handleRouting();
  }

  handleRouting() {
    const hash = window.location.hash || '';
    const chapterMatch = hash.match(/^#\/node\/([A-Z0-9_]+)\/chapter$/);
    if (chapterMatch) {
      const nodeId = chapterMatch[1];
      this.openReadingView(nodeId);
      return;
    }

    const nodeMatch = hash.match(/^#\/node\/([A-Z0-9_]+)$/);
    if (nodeMatch) {
      const nodeId = nodeMatch[1];
      this.closeReadingView();
      this.selectNode(nodeId, false);
      return;
    }

    // Default: tree view
    this.closeReadingView();
    if (this.drawerEl?.open) {
      this.closeDrawer(false);
    }
  }

  async openReadingView(nodeId) {
    const node = this.engine.nodesMap.get(nodeId);
    if (!node) {
      window.location.hash = '#/';
      return;
    }

    this.selectedNodeId = nodeId;
    if (this.drawerEl?.open) {
      this.drawerEl.close();
    }

    if (this.viewportEl) this.viewportEl.classList.add('hidden');
    if (this.readingViewEl) this.readingViewEl.classList.remove('hidden');

    const tierBadge = document.getElementById('reading-tier-badge');
    const catBadge = document.getElementById('reading-category-badge');
    const statusBadge = document.getElementById('reading-status-badge');
    const state = this.nodeStates[node.id] || 'locked';
    const category = this.engine.categories.get(node.category);

    if (tierBadge) tierBadge.textContent = `Tier ${node.tier}`;
    if (catBadge) {
      catBadge.textContent = category?.name || node.category;
      catBadge.style.backgroundColor = category?.color || '#3b82f6';
    }
    if (statusBadge) {
      statusBadge.textContent = state.toUpperCase();
      statusBadge.className = `badge badge-status ${state}`;
    }

    if (this.readingBackLinkEl) {
      this.readingBackLinkEl.href = `#/node/${node.id}`;
      this.readingBackLinkEl.onclick = (e) => {
        e.preventDefault();
        if (window.history.length > 1) {
          window.history.back();
        } else {
          window.location.hash = `#/node/${node.id}`;
        }
      };
    }

    if (this.readingArticleEl) {
      this.readingArticleEl.innerHTML = '<div class="spec-text">Loading tutorial chapter...</div>';
      const chapterData = await this.loadChapter(node);
      if (chapterData.success) {
        this.readingArticleEl.innerHTML = this.renderMarkdown(chapterData.markdown);
      } else if (chapterData.type === 'coming_soon') {
        this.readingArticleEl.innerHTML = this.renderMarkdown(this.renderComingSoonMarkdown(node));
      } else {
        this.readingArticleEl.innerHTML = `
          <div class="chapter-error">
            <h2>⚠️ Chapter Load Error</h2>
            <p>${this.escapeHtml(chapterData.error)}</p>
          </div>
        `;
      }
    }

    this.readingViewEl?.scrollTo(0, 0);
    window.scrollTo(0, 0);
  }

  closeReadingView() {
    if (this.readingViewEl) this.readingViewEl.classList.add('hidden');
    if (this.viewportEl) this.viewportEl.classList.remove('hidden');
  }

  selectNode(nodeId, updateHash = true) {
    this.selectedNodeId = nodeId;
    const node = this.engine.nodesMap.get(nodeId);
    if (!node) return;

    if (updateHash && window.location.hash !== `#/node/${nodeId}`) {
      window.location.hash = `#/node/${nodeId}`;
      return;
    }

    // Highlight node on canvas
    this.renderNodes();

    this.populateDrawer(node);

    if (!this.drawerEl.open) {
      this.drawerEl.showModal();
    }
  }

  closeDrawer(updateHash = true) {
    if (this.drawerEl?.open) {
      this.drawerEl.close();
    }
    this.selectedNodeId = null;
    this.renderNodes();
    if (updateHash && window.location.hash.startsWith('#/node/') && !window.location.hash.includes('/chapter')) {
      window.location.hash = '#/';
    }
  }

  populateDrawer(node) {
    const state = this.nodeStates[node.id] || 'locked';
    const category = this.engine.categories.get(node.category);

    // Meta badges & header
    const tierBadge = document.getElementById('drawer-tier-badge');
    const catBadge = document.getElementById('drawer-category-badge');
    const statusBadge = document.getElementById('drawer-status-badge');
    const titleEl = document.getElementById('drawer-node-title');

    if (tierBadge) tierBadge.textContent = `Tier ${node.tier}`;
    if (catBadge) {
      catBadge.textContent = category?.name || node.category;
      catBadge.style.backgroundColor = category?.color || '#3b82f6';
    }
    if (statusBadge) {
      statusBadge.textContent = state.toUpperCase();
      statusBadge.className = `badge badge-status ${state}`;
    }
    if (titleEl) titleEl.textContent = node.name;

    // CTA Open Chapter
    const openBtn = document.getElementById('drawer-open-chapter-btn');
    if (openBtn) {
      openBtn.href = `#/node/${node.id}/chapter`;
      openBtn.onclick = (e) => {
        e.preventDefault();
        window.location.hash = `#/node/${node.id}/chapter`;
      };
    }

    // Tab 1: Chapter Preview & Specs
    const algoSkillEl = document.getElementById('drawer-algo-skill');
    const leanSkillEl = document.getElementById('drawer-lean-skill');
    const refModuleEl = document.getElementById('drawer-ref-module');
    const thmListEl = document.getElementById('drawer-theorems-list');
    const prereqsListEl = document.getElementById('drawer-prereqs-list');
    const unlocksListEl = document.getElementById('drawer-unlocks-list');

    if (algoSkillEl) algoSkillEl.textContent = node.algorithm_skill || 'N/A';
    if (leanSkillEl) leanSkillEl.textContent = node.lean_skill || 'N/A';
    if (refModuleEl) refModuleEl.textContent = node.reference_module || 'Planned Module';

    // Headline theorems
    if (thmListEl) {
      thmListEl.innerHTML = '';
      const thms = node.headline_theorems || [];
      if (thms.length === 0) {
        thmListEl.innerHTML = `<span class="spec-text" style="color: var(--text-dim);">No headline theorems defined yet.</span>`;
      } else {
        thms.forEach(t => {
          const div = document.createElement('div');
          div.className = 'theorem-item';
          div.innerHTML = `<span>${this.escapeHtml(t)}</span><span class="thm-badge">Audited ✓</span>`;
          thmListEl.appendChild(div);
        });
      }
    }

    // Prereqs chips
    if (prereqsListEl) {
      prereqsListEl.innerHTML = '';
      const prereqs = node.prerequisites || [];
      if (prereqs.length === 0) {
        prereqsListEl.innerHTML = `<span class="spec-text" style="color: var(--text-dim);">None (Root Entry Point)</span>`;
      } else {
        prereqs.forEach(pId => {
          const chip = document.createElement('button');
          chip.className = 'dep-chip';
          chip.textContent = `${pId} (${this.nodeStates[pId] || 'locked'})`;
          chip.title = `Inspect ${pId}`;
          chip.addEventListener('click', () => this.selectNode(pId));
          prereqsListEl.appendChild(chip);
        });
      }
    }

    // Unlocks chips
    if (unlocksListEl) {
      unlocksListEl.innerHTML = '';
      const unlocks = node.unlocks || [];
      if (unlocks.length === 0) {
        unlocksListEl.innerHTML = `<span class="spec-text" style="color: var(--text-dim);">None (Terminal Leaf)</span>`;
      } else {
        unlocks.forEach(uId => {
          const chip = document.createElement('button');
          chip.className = 'dep-chip';
          chip.textContent = `${uId} (${this.nodeStates[uId] || 'locked'})`;
          chip.title = `Inspect ${uId}`;
          chip.addEventListener('click', () => this.selectNode(uId));
          unlocksListEl.appendChild(chip);
        });
      }
    }

    // Chapter Preview in drawer
    this.renderChapterPreview(node);

    // Tab 2: Exercises
    this.renderExercisesTab(node);
  }

  async renderChapterPreview(node) {
    const previewEl = document.getElementById('drawer-chapter-preview');
    if (!previewEl) return;
    previewEl.innerHTML = '<span class="spec-text">Loading preview...</span>';

    const chapterData = await this.loadChapter(node);
    if (chapterData.success) {
      const lines = chapterData.markdown.split('\n');
      const excerptLines = [];
      let count = 0;
      for (const line of lines) {
        excerptLines.push(line);
        count += line.length;
        if (count > 1200) break;
      }
      previewEl.innerHTML = this.renderMarkdown(excerptLines.join('\n') + '\n\n*(Click "Open Full Chapter" above to view complete tutorial)*');
    } else if (chapterData.type === 'coming_soon') {
      previewEl.innerHTML = this.renderMarkdown(this.renderComingSoonMarkdown(node));
    } else {
      previewEl.innerHTML = `<div class="chapter-error"><p>${this.escapeHtml(chapterData.error)}</p></div>`;
    }
  }

  renderExercisesTab(node) {
    this.renderQuizTab(node);
  }

  // ----------------------------------------------------------------------------
  // Homework Verifier Engine
  // ----------------------------------------------------------------------------
  renderQuizTab(node) {
    const quizContainer = document.getElementById('quiz-container');
    if (!quizContainer) return;
    quizContainer.innerHTML = '';

    const exercises = node.exercises || {};
    const predicts = exercises.predict || [];
    const fakes = exercises.spot_the_fake || [];

    if (predicts.length === 0 && fakes.length === 0) {
      quizContainer.innerHTML = `
        <div class="spec-card">
          <p class="spec-text" style="color: var(--text-muted);">
            No interactive exercises attached to this planned or reference module yet.
          </p>
        </div>
      `;
      return;
    }

    // Check if node is locked: prohibition on active quiz forms
    const nodeState = this.nodeStates[node.id] || 'locked';
    if (nodeState === 'locked') {
      const prereqs = node.prerequisites || [];
      const unsatisfied = prereqs.filter(p => !this.engine.masteredNodes.has(p));
      const prereqNames = unsatisfied.map(p => this.engine.nodesMap.get(p)?.name || p).join(', ') || 'prerequisite modules';
      const banner = document.createElement('div');
      banner.className = 'spec-card locked-warning';
      banner.style.borderColor = '#ef4444';
      banner.style.background = 'rgba(239, 68, 68, 0.08)';
      banner.innerHTML = `
        <div style="display: flex; align-items: center; gap: 12px; margin-bottom: 8px;">
          <span style="font-size: 24px;">🔒</span>
          <h3 style="color: #f87171; margin: 0; font-size: 16px;">Module Locked</h3>
        </div>
        <p class="spec-text" style="color: var(--text-color); margin-bottom: 8px;">
          All prerequisites must be mastered before homework verification is accessible.
        </p>
        <p class="spec-text" style="color: var(--text-dim); margin: 0; font-size: 13px;">
          Unsatisfied prerequisites: <strong>${this.escapeHTML(prereqNames)}</strong>
        </p>
      `;
      quizContainer.appendChild(banner);
      return;
    }

    // Check if node is already mastered
    const isMastered = this.engine.masteredNodes.has(node.id);
    if (isMastered) {
      const banner = document.createElement('div');
      banner.className = 'mastery-banner';
      banner.innerHTML = `
        <span style="font-size: 32px;">🏆</span>
        <div class="mastery-banner-title">Module Mastered!</div>
        <p class="mastery-banner-desc">You have successfully mastered ${node.name}. Downstream dependencies have unlocked across the skill tree.</p>
      `;
      quizContainer.appendChild(banner);
    }

    // 1. Predict Exercises
    predicts.forEach((q, idx) => {
      const savedAns = this.engine.getRecordedAnswer(node.id, 'predict', q.id);
      const isCorrect = savedAns && (savedAns.toLowerCase() === String(q.expected_answer).trim().toLowerCase());

      const card = document.createElement('div');
      card.className = `quiz-card ${isCorrect ? 'is-passed' : (savedAns ? 'is-failed' : '')}`;
      card.id = `quiz-${q.id}`;

      card.innerHTML = `
        <div class="quiz-header">
          <span class="quiz-type-badge predict">Challenge #${idx + 1}: Predict</span>
          <span class="quiz-status-badge">${isCorrect ? 'Passed ✓' : 'Pending'}</span>
        </div>
        <p class="quiz-prompt">${q.prompt}</p>
        <form class="predict-form" onsubmit="return false;">
          <input type="${q.input_type || 'text'}" class="predict-input" placeholder="Enter evaluation result..." value="${this.escapeHTML(savedAns || '')}" ${isCorrect ? 'readonly' : ''}>
          <button type="submit" class="btn btn-primary" ${isCorrect ? 'disabled' : ''}>
            ${isCorrect ? 'Solved ✓' : 'Submit'}
          </button>
        </form>
        <div class="quiz-feedback ${savedAns ? 'show ' + (isCorrect ? 'success' : 'error') : ''}">
          ${savedAns ? (isCorrect ? `<strong>✓ Correct!</strong> ${q.explanation}` : `<strong>✕ Incorrect.</strong> ${q.explanation}`) : ''}
        </div>
      `;

      const form = card.querySelector('.predict-form');
      const input = card.querySelector('.predict-input');
      const feedback = card.querySelector('.quiz-feedback');
      const submitBtn = form.querySelector('button');

      form.addEventListener('submit', () => {
        const val = input.value.trim();
        if (!val) {
          feedback.className = 'quiz-feedback show error';
          feedback.innerHTML = '<strong>Warning:</strong> Answer cannot be empty.';
          return;
        }

        const matches = (val.toLowerCase() === String(q.expected_answer).trim().toLowerCase());
        this.engine.recordAnswer(node.id, 'predict', q.id, val);

        if (matches) {
          card.className = 'quiz-card is-passed';
          feedback.className = 'quiz-feedback show success';
          feedback.innerHTML = `<strong>✓ Correct!</strong> ${q.explanation}`;
          submitBtn.disabled = true;
          submitBtn.textContent = 'Solved ✓';
          this.checkNodeCompletion(node.id);
        } else {
          card.className = 'quiz-card is-failed';
          feedback.className = 'quiz-feedback show error';
          feedback.innerHTML = `<strong>✕ Incorrect.</strong> ${q.explanation}`;
        }
      });

      quizContainer.appendChild(card);
    });

    // 2. Spot the Fake Exercises
    fakes.forEach((q, idx) => {
      const savedAns = this.engine.getRecordedAnswer(node.id, 'spot_the_fake', q.id);
      const correctOptionId = q.correct_option_id || q.options?.find(o => !o.is_fake)?.id;
      const isCorrect = savedAns && (savedAns.toLowerCase() === String(correctOptionId).trim().toLowerCase());

      const card = document.createElement('div');
      card.className = `quiz-card ${isCorrect ? 'is-passed' : (savedAns ? 'is-failed' : '')}`;
      card.id = `quiz-${q.id}`;

      let optionsHtml = '';
      (q.options || []).forEach(opt => {
        const isSelected = (savedAns === opt.id);
        let optionClass = '';
        if (isSelected) {
          optionClass = (opt.id === correctOptionId) ? 'option-correct' : 'option-incorrect';
        }
        optionsHtml += `
          <div class="option-item ${isSelected ? 'selected ' + optionClass : ''}" data-option-id="${opt.id}">
            <span class="option-key">(${opt.id.toUpperCase()})</span>
            <div class="option-code">${this.escapeHtml(opt.text)}</div>
          </div>
        `;
      });

      card.innerHTML = `
        <div class="quiz-header">
          <span class="quiz-type-badge spot-the-fake">Audit Challenge: Spot the Fake</span>
          <span class="quiz-status-badge">${isCorrect ? 'Passed ✓' : 'Pending'}</span>
        </div>
        <p class="quiz-prompt">${q.prompt}</p>
        <div class="options-list">${optionsHtml}</div>
        <div class="quiz-feedback ${savedAns ? 'show ' + (isCorrect ? 'success' : 'error') : ''}">
          ${savedAns ? this.getSpotTheFakeFeedback(q, savedAns, correctOptionId) : ''}
        </div>
      `;

      const optionItems = card.querySelectorAll('.option-item');
      const feedback = card.querySelector('.quiz-feedback');

      optionItems.forEach(item => {
        item.addEventListener('click', () => {
          const optId = item.dataset.optionId;
          const chosenOpt = q.options.find(o => o.id === optId);
          const chosenIsCorrect = (optId === correctOptionId);

          this.engine.recordAnswer(node.id, 'spot_the_fake', q.id, optId);

          // Update option styles
          optionItems.forEach(el => {
            el.className = 'option-item';
            if (el.dataset.optionId === optId) {
              el.classList.add('selected', chosenIsCorrect ? 'option-correct' : 'option-incorrect');
            }
          });

          card.className = `quiz-card ${chosenIsCorrect ? 'is-passed' : 'is-failed'}`;
          feedback.className = `quiz-feedback show ${chosenIsCorrect ? 'success' : 'error'}`;
          feedback.innerHTML = this.getSpotTheFakeFeedback(q, optId, correctOptionId);

          if (chosenIsCorrect) {
            this.checkNodeCompletion(node.id);
          }
        });
      });

      quizContainer.appendChild(card);
    });
  }

  getSpotTheFakeFeedback(question, chosenId, correctId) {
    const chosen = question.options?.find(o => o.id === chosenId);
    const isCorrect = (chosenId === correctId);
    let msg = '';
    if (isCorrect) {
      msg = `<strong>✓ Excellent Audit!</strong> ${chosen?.explanation || ''}`;
      if (question.summary_explanation) {
        msg += `<br><br><em>Takeaway:</em> ${question.summary_explanation}`;
      }
    } else {
      msg = `<strong>✕ Flawed Statement Selected:</strong> ${chosen?.explanation || 'This formulation contains an anti-pattern or circular definition.'}`;
    }
    return msg;
  }

  checkNodeCompletion(nodeId) {
    if (this.engine.isNodeCompleted(nodeId)) {
      const unlockedNew = this.engine.markNodeMastered(nodeId);
      if (unlockedNew) {
        this.nodeStates = this.engine.computeNodeStates();
        this.render();
        this.updateHUD();

        const node = this.engine.nodesMap.get(nodeId);
        this.showToast(`🎉 Mastered ${node?.name || nodeId}! Downstream nodes unlocked.`, 'success');

        // Re-render quiz tab with celebration banner
        if (node) this.renderQuizTab(node);
      }
    }
  }

  // ----------------------------------------------------------------------------
  // Tutorial Chapter Loader & Markdown Viewer
  // ----------------------------------------------------------------------------
  async loadChapter(node) {
    const filename = node.chapter_path ? node.chapter_path.split('/').pop() : `${node.id.toLowerCase()}.md`;
    const paths = [
      `chapters/${filename}`,
      `chapters/${node.id}.md`,
      `tutorial/${filename}`,
      node.chapter_path
    ];

    let content = null;
    let lastError = null;

    for (const p of paths) {
      if (!p) continue;
      try {
        const res = await fetch(p);
        if (res.ok) {
          content = await res.text();
          break;
        } else {
          lastError = `HTTP ${res.status}: ${res.statusText}`;
        }
      } catch (err) {
        lastError = err.message || String(err);
      }
    }

    if (content) {
      return { success: true, markdown: content };
    }

    const pilotChapters = ['BGCD', 'EUC', 'INS'];
    const isPilot = pilotChapters.includes(node.id) || Boolean(node.has_chapter);

    if (isPilot) {
      return {
        success: false,
        type: 'error',
        error: `Failed to load chapter for "${node.name}" from ${paths[0]} (${lastError || 'File not found'}).`
      };
    }

    return {
      success: false,
      type: 'coming_soon'
    };
  }

  renderComingSoonMarkdown(node) {
    const thms = (node.headline_theorems || []).map(t => `- \`${t}\``).join('\n') || '- None currently defined (Planned module)';
    const prereqs = (node.prerequisites || []).map(p => `- Node \`${p}\``).join('\n') || '- None (Root entry point)';
    const unlocks = (node.unlocks || []).map(u => `- Node \`${u}\``).join('\n') || '- Terminal leaf node';

    return `
# Chapter coming soon

A full interactive tutorial chapter for **${node.name}** is currently in development.

## Curriculum Metadata (from \`tree.json\`)

- **Algorithm Skill**: ${node.algorithm_skill || 'N/A'}
- **Lean Reading Skill**: ${node.lean_skill || 'N/A'}
- **Reference Module**: \`${node.reference_module || 'Planned Module'}\`

### Prerequisites
${prereqs}

### Downstream Unlocks
${unlocks}

### Headline Theorems
${thms}
    `.trim();
  }

  // Lightweight, zero-dependency Markdown parser with Lean syntax token highlighting
  renderMarkdown(text) {
    if (!text) return '';

    // Extract code blocks first to protect from inline formatting
    const codeBlocks = [];
    let md = text.replace(/```([a-zA-Z0-9_]*)\n([\s\S]*?)```/g, (match, lang, code) => {
      const idx = codeBlocks.length;
      let highlighted = this.escapeHtml(code);
      if (lang === 'lean' || lang === 'lean4' || !lang) {
        highlighted = this.highlightLeanSyntax(highlighted);
      }
      codeBlocks.push(`<pre><code class="language-${lang || 'lean'}">${highlighted}</code></pre>`);
      return `%%CODEBLOCK_${idx}%%`;
    });

    // Escape HTML outside code blocks
    md = this.escapeHtml(md);

    // Blockquotes
    md = md.replace(/^>\s?(.*)$/gm, '<blockquote>$1</blockquote>');

    // Headers
    md = md.replace(/^### (.*$)/gm, '<h3>$1</h3>');
    md = md.replace(/^## (.*$)/gm, '<h2>$1</h2>');
    md = md.replace(/^# (.*$)/gm, '<h1>$1</h1>');

    // Bold & Italics
    md = md.replace(/\*\*(.*?)\*\*/g, '<strong>$1</strong>');
    md = md.replace(/\*(.*?)\*/g, '<em>$1</em>');

    // Inline Code
    md = md.replace(/`([^`]+)`/g, '<code>$1</code>');

    // Unordered list items
    md = md.replace(/^- (.*$)/gm, '<li>$1</li>');
    md = md.replace(/(<li>[\s\S]*?<\/li>)/g, '<ul>$1</ul>');

    // Paragraphs
    md = md.split('\n\n').map(p => {
      p = p.trim();
      if (!p) return '';
      if (p.startsWith('<h') || p.startsWith('<pre') || p.startsWith('<ul') || p.startsWith('<blockquote') || p.startsWith('%%CODEBLOCK')) {
        return p;
      }
      return `<p>${p.replace(/\n/g, '<br>')}</p>`;
    }).join('\n');

    // Restore code blocks
    md = md.replace(/%%CODEBLOCK_(\d+)%%/g, (match, idx) => codeBlocks[idx] || '');

    return md;
  }

  highlightLeanSyntax(escapedCode) {
    const keywords = ['def', 'theorem', 'lemma', 'inductive', 'structure', 'where', 'by', 'intro', 'exact', 'apply', 'cases', 'induction', 'rcases', 'obtain', 'have', 'show', 'let', 'if', 'then', 'else', 'match', 'with', 'fun', 'example', 'open', 'namespace', 'import', 'variable', 'termination_by', 'decreasing_by'];
    const types = ['Nat', 'Int', 'List', 'String', 'Bool', 'Prop', 'Type', 'Option', 'Fin', 'Finset', 'Multiset', 'Array'];

    let out = escapedCode;

    // Comments (-- ...)
    out = out.replace(/(--.*$)/gm, '<span class="lean-comment">$1</span>');

    // Keywords
    const kwRegex = new RegExp(`\\b(${keywords.join('|')})\\b`, 'g');
    out = out.replace(kwRegex, '<span class="lean-keyword">$1</span>');

    // Types
    const typeRegex = new RegExp(`\\b(${types.join('|')})\\b`, 'g');
    out = out.replace(typeRegex, '<span class="lean-type">$1</span>');

    // Numeric literals
    out = out.replace(/\b(\d+)\b/g, '<span class="lean-number">$1</span>');

    return out;
  }

  escapeHTML(str) {
    if (str === null || str === undefined) return '';
    return String(str)
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#039;');
  }

  escapeHtml(str) {
    return this.escapeHTML(str);
  }

  // ----------------------------------------------------------------------------
  // Savefile Import / Export & Reset Handlers
  // ----------------------------------------------------------------------------
  setupSavefileHandlers() {
    // 1. Export savefile
    document.getElementById('btn-export-save')?.addEventListener('click', () => {
      const savefile = this.engine.exportSavefile();
      const blob = new Blob([JSON.stringify(savefile, null, 2)], { type: 'application/json' });
      const url = URL.createObjectURL(blob);
      const a = document.createElement('a');
      a.href = url;
      a.download = 'amort_save.json';
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
      URL.revokeObjectURL(url);
      this.showToast('💾 Savefile exported successfully as amort_save.json', 'success');
    });

    // 2. Import savefile via file input
    const fileInput = document.getElementById('file-import-save');
    fileInput?.addEventListener('change', (e) => {
      const file = e.target.files?.[0];
      if (file) {
        this.processSavefileUpload(file);
      }
      fileInput.value = ''; // Reset input
    });

    // 3. Drag & Drop across viewport
    const vp = this.viewportEl;
    const overlay = this.dropOverlayEl;

    window.addEventListener('dragover', (e) => {
      e.preventDefault();
      overlay.classList.add('is-active');
    });

    window.addEventListener('dragleave', (e) => {
      if (e.relatedTarget === null) {
        overlay.classList.remove('is-active');
      }
    });

    window.addEventListener('drop', (e) => {
      e.preventDefault();
      overlay.classList.remove('is-active');
      const file = e.dataTransfer?.files?.[0];
      if (file) {
        this.processSavefileUpload(file);
      }
    });

    // 4. Reset progress modal
    const resetBtn = document.getElementById('btn-reset-save');
    const resetDialog = this.resetModalEl;
    const cancelResetBtn = document.getElementById('btn-cancel-reset');
    const confirmResetBtn = document.getElementById('btn-confirm-reset');

    resetBtn?.addEventListener('click', () => {
      resetDialog?.showModal();
    });

    cancelResetBtn?.addEventListener('click', () => {
      resetDialog?.close();
    });

    confirmResetBtn?.addEventListener('click', () => {
      this.nodeStates = this.engine.resetProgress();
      this.render();
      this.updateHUD();
      resetDialog?.close();
      if (this.selectedNodeId) {
        const node = this.engine.nodesMap.get(this.selectedNodeId);
        if (node) this.populateDrawer(node);
      }
      this.showToast('↺ Progress reset to baseline.', 'success');
    });
  }

  processSavefileUpload(file) {
    const reader = new FileReader();
    reader.onload = (event) => {
      try {
        const parsed = JSON.parse(event.target.result);
        this.nodeStates = this.engine.importSavefile(parsed);
        this.render();
        this.updateHUD();
        if (this.selectedNodeId) {
          const node = this.engine.nodesMap.get(this.selectedNodeId);
          if (node) this.populateDrawer(node);
        }
        this.showToast(`✓ Savefile imported! ${this.engine.masteredNodes.size} nodes mastered.`, 'success');
      } catch (err) {
        console.error('Import savefile failed:', err);
        this.showToast(`Error: ${err.message || 'Invalid savefile'}`, 'error');
      }
    };
    reader.onerror = () => {
      this.showToast('Failed to read savefile.', 'error');
    };
    reader.readAsText(file);
  }

  // ----------------------------------------------------------------------------
  // General Event Listeners & Toast Notification
  // ----------------------------------------------------------------------------
  setupEventListeners() {
    window.addEventListener('resize', () => {
      this.renderWires();
    });

    window.addEventListener('keydown', (e) => {
      if (e.key === 'Escape') {
        this.closeDrawer();
      }
    });
  }

  showToast(message, type = 'success') {
    const container = document.getElementById('toast-container');
    if (!container) return;

    const toast = document.createElement('div');
    toast.className = `toast toast-${type}`;
    toast.textContent = message;
    container.appendChild(toast);

    setTimeout(() => {
      toast.style.opacity = '0';
      toast.style.transform = 'translateY(10px)';
      toast.style.transition = 'all 0.3s ease';
      setTimeout(() => toast.remove(), 300);
    }, 3800);
  }
}

// Expose classes on window for testability & integration
if (typeof window !== 'undefined') {
  window.SkillTreeEngine = SkillTreeEngine;
  window.SkillTreeApp = SkillTreeApp;
  window.ValueError = ValueError;
}

// Global initialization on DOM ready
document.addEventListener('DOMContentLoaded', () => {
  const app = new SkillTreeApp();
  window.__SKILL_TREE_APP__ = app;
  app.init().catch(err => {
    console.error('SkillTreeApp initialization error:', err);
  });
});
