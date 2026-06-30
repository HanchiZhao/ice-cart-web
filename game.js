/*
  叠冰塔 Ice Cart - 单文件核心逻辑
  玩法：移动小车接住随机下落的俄罗斯方块形冰块；方块只能旋转，不能左右移动；空中按俄罗斯方块节奏一格一格下落。
  计分：按小格计数。失败：按“大方块/整件方块”计数，掉出小车外达到 2 件则游戏结束。
*/

(function () {
  'use strict';

  window.addEventListener('load', () => {
    if (!window.Matter) {
      const canvas = document.getElementById('game');
      const ctx = canvas.getContext('2d');
      canvas.width = window.innerWidth * devicePixelRatio;
      canvas.height = window.innerHeight * devicePixelRatio;
      ctx.setTransform(devicePixelRatio, 0, 0, devicePixelRatio, 0, 0);
      ctx.fillStyle = '#6fb6c3';
      ctx.fillRect(0, 0, innerWidth, innerHeight);
      ctx.fillStyle = '#fff8df';
      ctx.font = '22px serif';
      ctx.textAlign = 'center';
      ctx.fillText('Matter.js 没有加载成功', innerWidth / 2, innerHeight / 2 - 18);
      ctx.font = '16px serif';
      ctx.fillText('请检查网络，或稍后刷新页面。', innerWidth / 2, innerHeight / 2 + 18);
      return;
    }
    new IceCartGame();
  });

  class IceCartGame {
    constructor() {
      this.M = window.Matter;
      this.Engine = this.M.Engine;
      this.World = this.M.World;
      this.Bodies = this.M.Bodies;
      this.Body = this.M.Body;
      this.Constraint = this.M.Constraint;
      this.Events = this.M.Events;
      this.Vector = this.M.Vector;

      this.canvas = document.getElementById('game');
      this.ctx = this.canvas.getContext('2d');
      this.dpr = Math.max(1, Math.min(3, window.devicePixelRatio || 1));

      // ====== 核心参数区：试玩后最容易调的都集中在这里 ======
      this.CELL = 30;                 // 一个小格的物理尺寸
      this.FREEZE_TIME = 16;          // 平滑稳定接触 16 秒后冻结
      this.MISS_LIMIT = 2;            // 掉出 2 个“大方块”后结束
      this.SPAWN_DELAY = 760;         // 一个方块落定后，下一个生成的延迟
      this.CART_WIDTH_RATIO = 0.62;   // 小车宽度占屏幕比例
      this.CART_MIN_WIDTH = 230;
      this.CART_MAX_WIDTH = 335;
      this.CART_WALL_H = 92;
      this.CART_FLOOR_H = 16;
      this.CART_MAX_SPEED = 1600;     // 只用于限制极端拖动输入，px/s
      this.GRAVITY = 0.86;
      this.GRID_FALL_INTERVAL = 0.58; // 普通下落：约每 0.58 秒下降一格
      this.FAST_GRID_INTERVAL = 0.075;// 按住“下落”：快速一格一格下降
      this.GRID_STEP_SMOOTH = 14;     // 格落动画平滑度；越大越贴近目标格
      this.MIN_CAMERA_SCALE = 0.36;
      this.MAX_CAMERA_SCALE = 1.0;
      this.FLAT_OVERLAP = 0.52;       // 平滑接触需要的切向重叠比例
      this.STABLE_SPEED = 1.15;       // 16 秒冻结计时的相对速度阈值
      this.STABLE_ANGULAR = 0.035;    // 16 秒冻结计时的角速度阈值

      this.engine = this.Engine.create({ enableSleeping: false });
      this.world = this.engine.world;
      this.engine.gravity.y = this.GRAVITY;
      this.engine.positionIterations = 8;
      this.engine.velocityIterations = 8;
      this.engine.constraintIterations = 4;

      this.W = 390;
      this.H = 844;
      this.cartY = 650;
      this.cartX = 195;
      this.cartTargetX = 195;
      this.cartVX = 0;
      this.cartMatterVX = 0;
      this.cartBodies = [];
      this.cartW = 280;

      this.pieces = new Map();
      this.activePiece = null;
      this.nextSpawnAt = 0;
      this.currentTime = 0;
      this.lastTS = 0;
      this.latestDT = 1 / 60;
      this.loadedCells = 0;
      this.missedPieces = 0;
      this.gameOver = false;
      this.gameStarted = true;

      this.cameraScale = 1;
      this.targetCameraScale = 1;
      this.activeFlatKeys = new Set();
      this.activeStableKeys = new Set();
      this.contactTimers = new Map();
      this.bonds = [];
      this.bondKeys = new Set();
      this.bondGraph = new Map();
      this.effects = [];

      this.draggingCart = false;
      this.dropHeld = false;
      this.pointerDown = false;
      this.lastPointer = { x: 0, y: 0 };

      this.shapes = this.makeShapeDefinitions();

      this.resize();
      window.addEventListener('resize', () => this.resize());
      window.addEventListener('orientationchange', () => setTimeout(() => this.resize(), 250));
      this.bindInput();
      this.createCart();
      this.bindPhysicsEvents();
      this.scheduleSpawn(100);
      requestAnimationFrame((ts) => this.loop(ts));
    }

    makeShapeDefinitions() {
      return [
        {
          id: 'O4', name: 'O', kind: 'ice', weight: 1.1,
          cells: [[0, 0], [1, 0], [0, 1], [1, 1]],
          palette: ['#7bd3be', '#62c7ac', '#a3ead9']
        },
        {
          id: 'L4', name: 'L', kind: 'ice', weight: 1.0,
          cells: [[0, -1], [0, 0], [0, 1], [1, 1]],
          palette: ['#bf87c7', '#a96abc', '#d8a6df']
        },
        {
          id: 'J4', name: 'J', kind: 'ice', weight: 1.0,
          cells: [[1, -1], [1, 0], [1, 1], [0, 1]],
          palette: ['#83d2e8', '#68bed8', '#b6eff7']
        },
        {
          id: 'I3', name: '三格I', kind: 'ice', weight: 0.85,
          cells: [[0, -1], [0, 0], [0, 1]],
          palette: ['#9fd9ff', '#71c4ee', '#d5f5ff']
        },
        {
          id: 'I4', name: '四格I', kind: 'ice', weight: 0.85,
          cells: [[0, -1.5], [0, -0.5], [0, 0.5], [0, 1.5]],
          palette: ['#f1b6d5', '#df8fbd', '#ffd6e9']
        },
        {
          id: 'T4', name: 'T', kind: 'ice', weight: 1.0,
          cells: [[-1, 0], [0, 0], [1, 0], [0, 1]],
          palette: ['#8cd7a9', '#63bf86', '#b8efcc']
        },
        {
          id: 'Z4', name: '闪电', kind: 'ice', weight: 0.95,
          cells: [[-1, 0], [0, 0], [0, 1], [1, 1]],
          palette: ['#a17dd1', '#815dbb', '#cdb6ed']
        },
        {
          id: 'S4', name: '倒闪电', kind: 'ice', weight: 0.95,
          cells: [[1, 0], [0, 0], [0, 1], [-1, 1]],
          palette: ['#c779a7', '#b55d8c', '#e7a5c7']
        },
        {
          id: 'QF1', name: '急冻', kind: 'quickFreeze', weight: 0.28,
          cells: [[0, 0]],
          palette: ['#7ef4f3', '#17dce0', '#f0ffff']
        },
        {
          id: 'DIRT_O4', name: '土方块', kind: 'dirt', weight: 0.42,
          cells: [[0, 0], [1, 0], [0, 1], [1, 1]],
          palette: ['#e4bf4d', '#c99a25', '#f6dd7a']
        }
      ];
    }

    resize() {
      this.W = Math.max(320, window.innerWidth || document.documentElement.clientWidth || 390);
      this.H = Math.max(520, window.innerHeight || document.documentElement.clientHeight || 844);
      this.canvas.width = Math.floor(this.W * this.dpr);
      this.canvas.height = Math.floor(this.H * this.dpr);
      this.canvas.style.width = this.W + 'px';
      this.canvas.style.height = this.H + 'px';
      this.ctx.setTransform(this.dpr, 0, 0, this.dpr, 0, 0);

      this.cartY = this.H - Math.max(178, Math.min(220, this.H * 0.22));
      this.cartW = this.clamp(this.W * this.CART_WIDTH_RATIO, this.CART_MIN_WIDTH, Math.min(this.CART_MAX_WIDTH, this.W - 70));
      if (!this.cartX) this.cartX = this.W / 2;
      this.cartX = this.clamp(this.cartX, this.cartW / 2 + 28, this.W - this.cartW / 2 - 28);
      this.cartTargetX = this.clamp(this.cartTargetX || this.cartX, this.cartW / 2 + 28, this.W - this.cartW / 2 - 28);
      if (this.cartBodies.length) this.placeCartBodies(this.cartX, this.cartY, 0);
    }

    bindInput() {
      const getPoint = (ev) => {
        const rect = this.canvas.getBoundingClientRect();
        return {
          x: ev.clientX - rect.left,
          y: ev.clientY - rect.top
        };
      };

      this.canvas.addEventListener('pointerdown', (ev) => {
        ev.preventDefault();
        this.canvas.setPointerCapture(ev.pointerId);
        const p = getPoint(ev);
        this.pointerDown = true;
        this.lastPointer = p;

        if (this.gameOver) {
          const b = this.getRestartButton();
          if (this.pointInRect(p, b)) this.restart();
          return;
        }

        const buttons = this.getButtons();
        if (this.pointInRect(p, buttons.drop)) {
          this.dropHeld = true;
          return;
        }
        if (this.pointInRect(p, buttons.rotate)) {
          this.rotateActivePiece();
          return;
        }

        this.draggingCart = true;
        this.cartTargetX = this.screenToWorldX(p.x);
      }, { passive: false });

      this.canvas.addEventListener('pointermove', (ev) => {
        ev.preventDefault();
        const p = getPoint(ev);
        this.lastPointer = p;
        if (this.draggingCart && !this.gameOver) {
          this.cartTargetX = this.screenToWorldX(p.x);
        }
      }, { passive: false });

      const endPointer = (ev) => {
        ev.preventDefault();
        this.pointerDown = false;
        this.draggingCart = false;
        this.dropHeld = false;
      };
      this.canvas.addEventListener('pointerup', endPointer, { passive: false });
      this.canvas.addEventListener('pointercancel', endPointer, { passive: false });
    }

    createCart() {
      this.cartBodies.forEach((b) => this.World.remove(this.world, b));
      this.cartBodies = [];
      const floor = this.Bodies.rectangle(this.cartX, this.cartY, this.cartW, this.CART_FLOOR_H, {
        isStatic: true,
        friction: 1.0,
        restitution: 0.02,
        label: 'cart_floor'
      });
      const left = this.Bodies.rectangle(this.cartX - this.cartW / 2 + 8, this.cartY - this.CART_WALL_H / 2, 16, this.CART_WALL_H, {
        isStatic: true,
        friction: 1.0,
        restitution: 0.02,
        label: 'cart_left'
      });
      const right = this.Bodies.rectangle(this.cartX + this.cartW / 2 - 8, this.cartY - this.CART_WALL_H / 2, 16, this.CART_WALL_H, {
        isStatic: true,
        friction: 1.0,
        restitution: 0.02,
        label: 'cart_right'
      });
      [floor, left, right].forEach((b) => {
        b.plugin.isCart = true;
        this.cartBodies.push(b);
      });
      this.World.add(this.world, this.cartBodies);
      this.placeCartBodies(this.cartX, this.cartY, 0);
    }

    placeCartBodies(x, y, matterVX) {
      const [floor, left, right] = this.cartBodies;
      if (!floor) return;
      this.Body.setPosition(floor, { x, y });
      this.Body.setPosition(left, { x: x - this.cartW / 2 + 8, y: y - this.CART_WALL_H / 2 });
      this.Body.setPosition(right, { x: x + this.cartW / 2 - 8, y: y - this.CART_WALL_H / 2 });
      this.cartBodies.forEach((b) => this.Body.setVelocity(b, { x: matterVX, y: 0 }));
    }

    bindPhysicsEvents() {
      this.Events.on(this.engine, 'collisionStart', (event) => this.handleCollisionPairs(event.pairs));
      this.Events.on(this.engine, 'collisionActive', (event) => this.handleCollisionPairs(event.pairs));
    }

    scheduleSpawn(delayMs) {
      this.nextSpawnAt = this.currentTime + delayMs / 1000;
    }

    spawnPiece() {
      if (this.gameOver) return;
      const def = this.weightedChoice(this.shapes);
      const margin = this.CELL * 2.2;
      const spawnX = this.random(margin, this.W - margin);
      const spawnY = this.screenToWorldY(82);
      const angle = Math.floor(this.random(0, 4)) * Math.PI / 2;
      const id = 'p' + Math.floor(Math.random() * 1e9).toString(36) + '_' + Date.now().toString(36);
      const parts = [];
      const cellSize = this.CELL * 0.995;

      for (let i = 0; i < def.cells.length; i++) {
        const [cx, cy] = def.cells[i];
        const part = this.Bodies.rectangle(spawnX + cx * this.CELL, spawnY + cy * this.CELL, cellSize, cellSize, {
          chamfer: { radius: 5 },
          friction: 0.96,
          frictionStatic: 1.0,
          frictionAir: 0.006,
          restitution: 0.035,
          density: def.kind === 'dirt' ? 0.0046 : 0.0028,
          label: 'piece_part'
        });
        parts.push(part);
      }

      let body;
      if (parts.length === 1) {
        body = parts[0];
      } else {
        body = this.Body.create({
          parts,
          friction: 0.96,
          frictionStatic: 1.0,
          frictionAir: 0.006,
          restitution: 0.035,
          density: def.kind === 'dirt' ? 0.0046 : 0.0028,
          label: 'piece'
        });
      }
      this.Body.setAngle(body, angle);
      this.Body.setVelocity(body, { x: 0, y: 0 });
      this.Body.setAngularVelocity(body, 0);

      const visualParts = body.parts.length > 1 ? body.parts.slice(1) : [body];
      const visualCells = visualParts.map((part) => this.worldOffsetToLocal(body, part.position.x - body.position.x, part.position.y - body.position.y));
      const cellData = visualCells.map((_, i) => ({
        cracks: this.makeCracks(i + body.id * 17),
        wobble: this.random(0, Math.PI * 2)
      }));

      body.plugin.piece = {
        id,
        defId: def.id,
        name: def.name,
        kind: def.kind,
        cellCount: def.cells.length,
        palette: def.palette,
        frozen: false,
        touchedStack: false,
        missed: false,
        settled: false,
        active: true,
        inAir: true,
        releasedAt: 0,
        dropTimer: 0,
        airTargetY: body.position.y,
        cartLocked: false,
        lockRel: null,
        bornAt: this.currentTime,
        visualParts,
        visualCells,
        shapeCells: def.cells.map((c) => [c[0], c[1]]),
        cellData,
        frostedAt: 0
      };

      // 空中阶段不交给自由落体，也不允许重心导致自转。
      // 它会像俄罗斯方块一样按格下落；第一次接触小车/堆叠体后才释放为真实物理刚体。
      this.Body.setStatic(body, true);
      this.pieces.set(body.id, body);
      this.World.add(this.world, body);
      this.activePiece = body;
      this.effects.push({ type: 'spawn', x: spawnX, y: spawnY, t: 0, life: 0.45 });
    }

    loop(ts) {
      if (!this.lastTS) this.lastTS = ts;
      let dt = (ts - this.lastTS) / 1000;
      this.lastTS = ts;
      dt = this.clamp(dt, 1 / 120, 1 / 30);
      this.latestDT = dt;
      this.currentTime += dt;

      if (!this.gameOver) {
        this.updateCart(dt);
        this.updateLockedBodies();

        if (this.nextSpawnAt && this.currentTime >= this.nextSpawnAt && !this.activePiece) {
          this.nextSpawnAt = 0;
          this.spawnPiece();
        } else if (this.nextSpawnAt && this.currentTime >= this.nextSpawnAt && this.activePiece === null) {
          this.nextSpawnAt = 0;
          this.spawnPiece();
        } else if (!this.activePiece && !this.nextSpawnAt) {
          this.scheduleSpawn(250);
        }

        this.updateActiveKinematicPiece(dt);

        this.activeFlatKeys.clear();
        this.activeStableKeys.clear();
        this.Engine.update(this.engine, dt * 1000);
        this.updateLockedBodies();
        this.cleanupContactTimers();
        this.updatePieceStates(dt);
        this.updateCamera(dt);
        this.updateEffects(dt);
      } else {
        this.updateEffects(dt);
      }

      this.draw();
      requestAnimationFrame((next) => this.loop(next));
    }

    updateCart(dt) {
      const minX = this.cartW / 2 + 24;
      const maxX = this.W - this.cartW / 2 - 24;
      this.cartTargetX = this.clamp(this.cartTargetX, minX, maxX);
      const oldX = this.cartX;

      // 新手感：小车实时跟随手指，不再用弹簧慢慢追。
      // 但仍把本帧位移换算成物理速度，车内方块会受到急停、急拉带来的惯性影响。
      this.cartX = this.cartTargetX;
      this.cartX = this.clamp(this.cartX, minX, maxX);
      const dx = this.cartX - oldX;
      this.cartVX = dt > 0 ? this.clamp(dx / dt, -this.CART_MAX_SPEED, this.CART_MAX_SPEED) : 0;
      this.cartMatterVX = dt > 0 ? this.clamp(dx / (dt * 60), -26, 26) : 0;
      this.placeCartBodies(this.cartX, this.cartY, this.cartMatterVX);
    }

    updateActiveKinematicPiece(dt) {
      const body = this.activePiece;
      if (!body || this.gameOver) return;
      const p = body.plugin.piece;
      if (!p || !p.inAir || p.missed || p.cartLocked) return;

      const interval = this.dropHeld ? this.FAST_GRID_INTERVAL : this.GRID_FALL_INTERVAL;
      p.dropTimer += dt;
      while (p.dropTimer >= interval) {
        p.dropTimer -= interval;
        p.airTargetY += this.CELL;
      }

      const smooth = 1 - Math.pow(0.0008, dt * this.GRID_STEP_SMOOTH);
      const nextY = body.position.y + (p.airTargetY - body.position.y) * smooth;
      this.Body.setPosition(body, { x: body.position.x, y: nextY });
      this.Body.setVelocity(body, { x: 0, y: 0 });
      this.Body.setAngularVelocity(body, 0);
    }

    releasePiecePhysics(body) {
      const p = body && body.plugin ? body.plugin.piece : null;
      if (!p || !p.inAir || p.missed) return;
      p.inAir = false;
      p.releasedAt = this.currentTime;
      p.airTargetY = body.position.y;
      this.Body.setStatic(body, false);
      this.Body.setVelocity(body, { x: 0, y: 0.35 });
      this.Body.setAngularVelocity(body, 0);
      this.effects.push({ type: 'land', x: body.position.x, y: body.position.y, t: 0, life: 0.28 });
    }

    updateLockedBodies() {
      for (const body of this.pieces.values()) {
        const p = body.plugin.piece;
        if (!p || !p.cartLocked || !p.lockRel || p.missed) continue;
        this.Body.setPosition(body, {
          x: this.cartX + p.lockRel.x,
          y: this.cartY + p.lockRel.y
        });
        this.Body.setAngle(body, p.lockRel.angle);
        this.Body.setVelocity(body, { x: this.cartMatterVX, y: 0 });
        this.Body.setAngularVelocity(body, 0);
      }
    }

    updatePieceStates() {
      let cells = 0;
      let currentTop = this.cartY;
      for (const body of Array.from(this.pieces.values())) {
        const p = body.plugin.piece;
        if (!p || p.missed) continue;

        if (body.bounds.min.y < currentTop) currentTop = body.bounds.min.y;

        const belowCart = body.bounds.min.y > this.cartY + 120;
        const farSide = body.position.x < -this.CELL * 2 || body.position.x > this.W + this.CELL * 2;
        const droppedTooLow = body.position.y > this.cartY + 180;
        if (belowCart || farSide || droppedTooLow) {
          this.markMissed(body);
          continue;
        }

        const overlapsCartWidth = body.bounds.max.x > this.cartX - this.cartW / 2 - 12 && body.bounds.min.x < this.cartX + this.cartW / 2 + 12;
        const aboveCartFloor = body.bounds.max.y < this.cartY + 52;
        if ((p.touchedStack || p.cartLocked) && overlapsCartWidth && aboveCartFloor) {
          cells += p.cellCount;
        }

        if (this.activePiece === body) {
          const hasContact = p.touchedStack;
          const slowEnough = Math.abs(body.velocity.y) < 1.45 && this.Vector.magnitude(body.velocity) < 2.2;
          const livedEnough = !p.inAir && this.currentTime - Math.max(p.bornAt, p.releasedAt || 0) > 0.42;
          if (!p.inAir && hasContact && slowEnough && livedEnough) {
            p.settled = true;
            p.active = false;
            this.activePiece = null;
            this.scheduleSpawn(this.SPAWN_DELAY);
          }
        }
      }
      this.loadedCells = cells;
    }

    updateCamera(dt) {
      let top = this.cartY - 160;
      for (const body of this.pieces.values()) {
        const p = body.plugin.piece;
        if (p && !p.missed && (p.touchedStack || p.cartLocked)) top = Math.min(top, body.bounds.min.y);
      }
      const desiredWorldHeight = Math.max(360, this.cartY - top + 210);
      const available = Math.max(330, this.H - 200);
      this.targetCameraScale = this.clamp(available / desiredWorldHeight, this.MIN_CAMERA_SCALE, this.MAX_CAMERA_SCALE);
      const smooth = 1 - Math.pow(0.06, dt);
      this.cameraScale += (this.targetCameraScale - this.cameraScale) * smooth;
    }

    updateEffects(dt) {
      for (const e of this.effects) e.t += dt;
      this.effects = this.effects.filter((e) => e.t < e.life);
    }

    markMissed(body) {
      const p = body.plugin.piece;
      if (!p || p.missed) return;
      p.missed = true;
      if (this.activePiece === body) {
        this.activePiece = null;
        this.scheduleSpawn(this.SPAWN_DELAY);
      }
      this.missedPieces += 1;
      this.effects.push({ type: 'miss', x: body.position.x, y: body.position.y, t: 0, life: 0.7 });
      this.World.remove(this.world, body);
      this.pieces.delete(body.id);
      if (this.missedPieces >= this.MISS_LIMIT) {
        this.gameOver = true;
        this.activePiece = null;
      }
    }

    rotateActivePiece() {
      if (!this.activePiece || this.gameOver) return;
      const p = this.activePiece.plugin.piece;
      // 只有仍在空中、仍按俄罗斯方块方式下落时可以旋转；接触后交给物理，不再强行拧动。
      if (!p || !p.active || !p.inAir || p.cartLocked) return;
      this.Body.rotate(this.activePiece, Math.PI / 2);
      this.Body.setVelocity(this.activePiece, { x: 0, y: 0 });
      this.Body.setAngularVelocity(this.activePiece, 0);
      this.effects.push({ type: 'rotate', x: this.activePiece.position.x, y: this.activePiece.position.y, t: 0, life: 0.22 });
    }

    handleCollisionPairs(pairs) {
      for (const pair of pairs) {
        const entA = this.getEntity(pair.bodyA);
        const entB = this.getEntity(pair.bodyB);
        if (!entA || !entB || entA.key === entB.key) continue;

        const flat = this.isFlatContact(pair, entA, entB);
        const stable = flat && this.isStableContact(entA, entB);
        const key = this.contactKey(entA, entB);

        if (flat) this.activeFlatKeys.add(key);
        if (stable) this.activeStableKeys.add(key);

        // 空中方块第一次接触小车/堆叠体后，才从“俄罗斯方块格落模式”释放为真实物理刚体。
        if (entA.type === 'piece' && entA.body.plugin.piece.inAir && (entB.type === 'cart' || entB.type === 'piece')) this.releasePiecePhysics(entA.body);
        if (entB.type === 'piece' && entB.body.plugin.piece.inAir && (entA.type === 'cart' || entA.type === 'piece')) this.releasePiecePhysics(entB.body);

        // 标记已经接触到小车/堆叠体，方便计分和生成下一个方块。
        if (entA.type === 'piece' && (entB.type === 'cart' || entB.type === 'piece')) entA.body.plugin.piece.touchedStack = true;
        if (entB.type === 'piece' && (entA.type === 'cart' || entA.type === 'piece')) entB.body.plugin.piece.touchedStack = true;

        // 急冻方块：只要和其他方块产生平滑接触，目标和自己立即冻结；角搭不触发。
        if (flat && entA.type === 'piece' && entB.type === 'piece') {
          this.tryQuickFreeze(entA.body, entB.body);
          this.tryQuickFreeze(entB.body, entA.body);
        }

        if (stable && this.canNormalFreeze(entA, entB)) {
          const rec = this.contactTimers.get(key) || { t: 0, a: entA, b: entB };
          rec.t += this.latestDT;
          rec.a = entA;
          rec.b = entB;
          this.contactTimers.set(key, rec);
          if (rec.t >= this.FREEZE_TIME) {
            this.freezeByStableContact(entA, entB);
            this.contactTimers.delete(key);
          }
        }
      }
    }

    cleanupContactTimers() {
      for (const [key, rec] of Array.from(this.contactTimers.entries())) {
        if (!this.activeStableKeys.has(key)) {
          rec.t -= this.latestDT * 2.2;
          if (rec.t <= 0) this.contactTimers.delete(key);
          else this.contactTimers.set(key, rec);
        }
      }
    }

    getEntity(body) {
      if (!body) return null;
      if (body.plugin && body.plugin.isCart) return { type: 'cart', body, key: 'cart' };
      const root = body.parent && body.parent !== body ? body.parent : body;
      if (root.plugin && root.plugin.piece && this.pieces.has(root.id)) return { type: 'piece', body: root, key: 'p:' + root.id };
      return null;
    }

    contactKey(a, b) {
      return [a.key, b.key].sort().join('|');
    }

    isFlatContact(pair, entA, entB) {
      const n = pair.collision && pair.collision.normal ? pair.collision.normal : { x: 0, y: 1 };
      const ax = Math.abs(n.x);
      const ay = Math.abs(n.y);
      if (Math.max(ax, ay) < 0.84) return false;

      const boundsA = entA.type === 'cart' ? pair.bodyA.bounds : entA.body.bounds;
      const boundsB = entB.type === 'cart' ? pair.bodyB.bounds : entB.body.bounds;

      let tangentOverlap;
      if (ay >= ax) {
        tangentOverlap = Math.min(boundsA.max.x, boundsB.max.x) - Math.max(boundsA.min.x, boundsB.min.x);
      } else {
        tangentOverlap = Math.min(boundsA.max.y, boundsB.max.y) - Math.max(boundsA.min.y, boundsB.min.y);
      }
      return tangentOverlap >= this.CELL * this.FLAT_OVERLAP;
    }

    isStableContact(entA, entB) {
      const va = entA.type === 'cart' ? { x: this.cartMatterVX, y: 0 } : entA.body.velocity;
      const vb = entB.type === 'cart' ? { x: this.cartMatterVX, y: 0 } : entB.body.velocity;
      const rv = this.Vector.magnitude(this.Vector.sub(va, vb));
      const aa = entA.type === 'cart' ? 0 : Math.abs(entA.body.angularVelocity || 0);
      const ab = entB.type === 'cart' ? 0 : Math.abs(entB.body.angularVelocity || 0);
      return rv < this.STABLE_SPEED && aa < this.STABLE_ANGULAR && ab < this.STABLE_ANGULAR;
    }

    canNormalFreeze(entA, entB) {
      if (entA.type === 'cart' && entB.type === 'piece') return entB.body.plugin.piece.kind !== 'dirt';
      if (entB.type === 'cart' && entA.type === 'piece') return entA.body.plugin.piece.kind !== 'dirt';
      if (entA.type === 'piece' && entB.type === 'piece') {
        const pa = entA.body.plugin.piece;
        const pb = entB.body.plugin.piece;
        return pa.kind !== 'dirt' && pb.kind !== 'dirt';
      }
      return false;
    }

    tryQuickFreeze(source, target) {
      const sp = source.plugin.piece;
      const tp = target.plugin.piece;
      if (!sp || !tp) return;
      if (sp.kind !== 'quickFreeze') return;
      if (tp.kind === 'dirt') {
        // 土方块永远不冻结；急冻方块也不会和土块建立固定冻结关系。
        return;
      }
      if (this.bondKeys.has(this.pieceBondKey(source, target))) return;
      this.setFrozen(source);
      this.setFrozen(target);
      this.createPieceBond(source, target, true);
      this.effects.push({ type: 'quickFreeze', x: target.position.x, y: target.position.y, t: 0, life: 0.55 });
    }

    freezeByStableContact(entA, entB) {
      if (entA.type === 'cart' && entB.type === 'piece') {
        this.setFrozen(entB.body);
        this.createCartBond(entB.body);
      } else if (entB.type === 'cart' && entA.type === 'piece') {
        this.setFrozen(entA.body);
        this.createCartBond(entA.body);
      } else if (entA.type === 'piece' && entB.type === 'piece') {
        this.setFrozen(entA.body);
        this.setFrozen(entB.body);
        this.createPieceBond(entA.body, entB.body, false);
      }
    }

    setFrozen(body) {
      const p = body.plugin.piece;
      if (!p || p.kind === 'dirt') return;
      if (!p.frozen) {
        p.frozen = true;
        p.frostedAt = this.currentTime;
        this.effects.push({ type: 'freeze', x: body.position.x, y: body.position.y, t: 0, life: 0.55 });
      }
    }

    pieceBondKey(a, b) {
      return ['p' + a.id, 'p' + b.id].sort().join('|');
    }

    createPieceBond(a, b, immediate) {
      if (!a || !b || a === b) return;
      const pa = a.plugin.piece;
      const pb = b.plugin.piece;
      if (!pa || !pb || pa.kind === 'dirt' || pb.kind === 'dirt') return;
      const key = this.pieceBondKey(a, b);
      if (this.bondKeys.has(key)) return;
      this.bondKeys.add(key);
      this.addGraphEdge(a.id, b.id);

      const dx = b.position.x - a.position.x;
      const dy = b.position.y - a.position.y;
      const dist = Math.max(8, Math.sqrt(dx * dx + dy * dy));
      const c1 = this.Constraint.create({
        bodyA: a,
        bodyB: b,
        pointA: { x: 0, y: 0 },
        pointB: { x: 0, y: 0 },
        length: dist,
        stiffness: immediate ? 0.98 : 0.9,
        damping: 0.08
      });
      const c2 = this.Constraint.create({
        bodyA: a,
        bodyB: b,
        pointA: { x: this.CELL * 0.38, y: this.CELL * 0.16 },
        pointB: { x: this.CELL * 0.38, y: this.CELL * 0.16 },
        length: dist,
        stiffness: immediate ? 0.86 : 0.74,
        damping: 0.1
      });
      this.World.add(this.world, [c1, c2]);
      this.bonds.push({ type: 'piece', a: a.id, b: b.id, constraints: [c1, c2] });

      if (pa.cartLocked || pb.cartLocked) this.lockClusterToCart(a);
    }

    createCartBond(piece) {
      const p = piece.plugin.piece;
      if (!p || p.kind === 'dirt') return;
      const key = ['cart', 'p' + piece.id].join('|');
      if (this.bondKeys.has(key)) return;
      this.bondKeys.add(key);
      this.addGraphEdge('cart', piece.id);
      this.bonds.push({ type: 'cart', a: 'cart', b: piece.id, constraints: [] });
      this.lockClusterToCart(piece);
      this.effects.push({ type: 'cartFreeze', x: piece.position.x, y: piece.position.y, t: 0, life: 0.65 });
    }

    addGraphEdge(a, b) {
      if (!this.bondGraph.has(a)) this.bondGraph.set(a, new Set());
      if (!this.bondGraph.has(b)) this.bondGraph.set(b, new Set());
      this.bondGraph.get(a).add(b);
      this.bondGraph.get(b).add(a);
    }

    lockClusterToCart(startPiece) {
      const startId = startPiece.id;
      const seen = new Set(['cart']);
      const queue = [startId];
      while (queue.length) {
        const id = queue.shift();
        if (seen.has(id)) continue;
        seen.add(id);
        const body = this.pieces.get(id);
        if (body && body.plugin && body.plugin.piece) {
          const p = body.plugin.piece;
          p.cartLocked = true;
          p.lockRel = {
            x: body.position.x - this.cartX,
            y: body.position.y - this.cartY,
            angle: body.angle
          };
          this.setFrozen(body);
        }
        const nb = this.bondGraph.get(id);
        if (nb) {
          for (const n of nb) {
            if (!seen.has(n)) queue.push(n);
          }
        }
      }
    }

    restart() {
      for (const body of this.pieces.values()) this.World.remove(this.world, body);
      for (const b of this.bonds) {
        if (b.constraints) b.constraints.forEach((c) => this.World.remove(this.world, c));
      }
      this.pieces.clear();
      this.contactTimers.clear();
      this.activeFlatKeys.clear();
      this.activeStableKeys.clear();
      this.bonds = [];
      this.bondKeys.clear();
      this.bondGraph.clear();
      this.effects = [];
      this.activePiece = null;
      this.loadedCells = 0;
      this.missedPieces = 0;
      this.gameOver = false;
      this.cameraScale = 1;
      this.targetCameraScale = 1;
      this.cartX = this.W / 2;
      this.cartTargetX = this.cartX;
      this.cartVX = 0;
      this.placeCartBodies(this.cartX, this.cartY, 0);
      this.scheduleSpawn(300);
    }

    // ====== 绘制区 ======
    draw() {
      const ctx = this.ctx;
      ctx.setTransform(this.dpr, 0, 0, this.dpr, 0, 0);
      ctx.clearRect(0, 0, this.W, this.H);
      this.drawBackground(ctx);
      this.drawWorld(ctx);
      this.drawEffects(ctx);
      this.drawUI(ctx);
      if (this.gameOver) this.drawGameOver(ctx);
    }

    drawBackground(ctx) {
      const grd = ctx.createLinearGradient(0, 0, 0, this.H);
      grd.addColorStop(0, '#7ac3d1');
      grd.addColorStop(0.65, '#74bcc7');
      grd.addColorStop(1, '#397887');
      ctx.fillStyle = grd;
      ctx.fillRect(0, 0, this.W, this.H);

      ctx.save();
      ctx.globalAlpha = 0.13;
      ctx.strokeStyle = '#4f96a2';
      ctx.lineWidth = 3;
      for (let i = 0; i < 34; i++) {
        const x = ((i * 73) % (this.W + 120)) - 60;
        const y = 40 + ((i * 117) % Math.max(100, this.H - 230));
        ctx.beginPath();
        ctx.ellipse(x, y, 26 + (i % 4) * 6, 13 + (i % 3) * 4, (i % 7) * 0.2, 0, Math.PI * 2);
        ctx.stroke();
      }
      ctx.restore();

      this.drawHangingCharm(ctx);
      this.drawSeaFloor(ctx);
    }

    drawHangingCharm(ctx) {
      const x = 44;
      const y = 12;
      ctx.save();
      ctx.lineCap = 'round';
      ctx.strokeStyle = '#33251f';
      ctx.lineWidth = 4;
      ctx.beginPath();
      ctx.moveTo(x + 10, 0);
      ctx.lineTo(x + 10, y + 55);
      ctx.stroke();

      ctx.fillStyle = '#f8dda4';
      ctx.strokeStyle = '#2f2724';
      ctx.lineWidth = 2.6;
      this.roundRect(ctx, x - 8, y + 40, 42, 84, 12, true, true);
      ctx.fillStyle = '#cf3e52';
      this.drawHeart(ctx, x + 14, y + 70, 11);
      this.drawHeart(ctx, x + 14, y + 104, 11);
      ctx.fillStyle = '#d7693a';
      ctx.beginPath();
      ctx.arc(x + 14, y + 132, 6, 0, Math.PI * 2);
      ctx.fill();
      ctx.strokeStyle = '#243139';
      ctx.lineWidth = 3;
      ctx.beginPath();
      ctx.moveTo(x + 5, y + 139);
      ctx.lineTo(x + 3, y + 178);
      ctx.moveTo(x + 14, y + 139);
      ctx.lineTo(x + 13, y + 181);
      ctx.moveTo(x + 23, y + 139);
      ctx.lineTo(x + 25, y + 176);
      ctx.stroke();
      ctx.restore();
    }

    drawSeaFloor(ctx) {
      ctx.save();
      const base = this.H - 54;
      ctx.fillStyle = '#246a76';
      ctx.fillRect(0, this.H - 78, this.W, 78);
      ctx.fillStyle = '#dfeef0';
      ctx.globalAlpha = 0.96;
      ctx.beginPath();
      ctx.moveTo(0, base - 22);
      for (let x = 0; x <= this.W; x += 24) {
        ctx.quadraticCurveTo(x + 12, base - 30 + Math.sin(x * 0.07) * 5, x + 24, base - 22);
      }
      ctx.lineTo(this.W, this.H);
      ctx.lineTo(0, this.H);
      ctx.closePath();
      ctx.fill();
      ctx.globalAlpha = 1;

      // 珊瑚与海草
      const coralY = this.H - 95;
      this.drawSeaweed(ctx, 24, coralY + 28, 0.9);
      this.drawSeaweed(ctx, this.W - 72, coralY + 24, 0.84);
      this.drawCoral(ctx, this.W * 0.50, coralY + 22, 1.05);
      this.drawTubeCoral(ctx, this.W * 0.18, coralY + 28, 0.8);
      this.drawTubeCoral(ctx, this.W * 0.82, coralY + 23, 0.8);
      ctx.restore();
    }

    drawSeaweed(ctx, x, y, s) {
      ctx.save();
      ctx.translate(x, y);
      ctx.scale(s, s);
      ctx.fillStyle = '#4ea85a';
      ctx.strokeStyle = '#1d673f';
      ctx.lineWidth = 3;
      for (let i = 0; i < 3; i++) {
        ctx.beginPath();
        ctx.moveTo(i * 16, 0);
        ctx.bezierCurveTo(i * 16 - 20, -24, i * 16 + 32, -42, i * 16 - 6, -68);
        ctx.bezierCurveTo(i * 16 + 6, -42, i * 16 + 34, -22, i * 16 + 8, 0);
        ctx.closePath();
        ctx.fill();
        ctx.stroke();
      }
      ctx.restore();
    }

    drawCoral(ctx, x, y, s) {
      ctx.save();
      ctx.translate(x, y);
      ctx.scale(s, s);
      ctx.strokeStyle = '#66c4c4';
      ctx.lineWidth = 7;
      ctx.lineCap = 'round';
      for (let i = -4; i <= 4; i++) {
        ctx.beginPath();
        ctx.moveTo(i * 9, 2);
        ctx.bezierCurveTo(i * 6, -28, i * 15, -44, i * 4, -66 - Math.abs(i) * 4);
        ctx.stroke();
      }
      ctx.strokeStyle = '#2f8b88';
      ctx.lineWidth = 2;
      ctx.stroke();
      ctx.restore();
    }

    drawTubeCoral(ctx, x, y, s) {
      ctx.save();
      ctx.translate(x, y);
      ctx.scale(s, s);
      ctx.strokeStyle = '#9b3a54';
      ctx.fillStyle = '#d85e78';
      ctx.lineWidth = 4;
      for (let i = 0; i < 3; i++) {
        ctx.beginPath();
        ctx.roundRect ? ctx.roundRect(i * 16, -54 - i * 6, 14, 54 + i * 6, 7) : this.roundRect(ctx, i * 16, -54 - i * 6, 14, 54 + i * 6, 7, true, true);
        ctx.fill();
        ctx.stroke();
        ctx.beginPath();
        ctx.ellipse(i * 16 + 7, -54 - i * 6, 7, 4, 0, 0, Math.PI * 2);
        ctx.stroke();
      }
      ctx.restore();
    }

    drawWorld(ctx) {
      // 先画小车后方鱼人，再画方块，再画小车前景。
      this.drawFishGuard(ctx, this.cartX - this.cartW / 2 - 33, this.cartY - 28, -1);
      this.drawFishGuard(ctx, this.cartX + this.cartW / 2 + 33, this.cartY - 28, 1);

      for (const body of this.pieces.values()) {
        const p = body.plugin.piece;
        if (!p || p.missed) continue;
        this.drawPiece(ctx, body);
      }
      this.drawCart(ctx);
    }

    worldToScreen(x, y) {
      const anchorY = this.H - 190;
      return {
        x: this.W / 2 + (x - this.W / 2) * this.cameraScale,
        y: anchorY + (y - this.cartY) * this.cameraScale
      };
    }

    screenToWorldX(x) {
      return this.W / 2 + (x - this.W / 2) / this.cameraScale;
    }

    screenToWorldY(y) {
      const anchorY = this.H - 190;
      return this.cartY + (y - anchorY) / this.cameraScale;
    }

    worldOffsetToLocal(body, dx, dy) {
      const a = -(body.angle || 0);
      const c = Math.cos(a);
      const s = Math.sin(a);
      return {
        x: dx * c - dy * s,
        y: dx * s + dy * c
      };
    }

    drawPiece(ctx, body) {
      const p = body.plugin.piece;
      const cells = p.visualCells || (p.visualParts || []).map((part) => this.worldOffsetToLocal(body, part.position.x - body.position.x, part.position.y - body.position.y));
      const pos = this.worldToScreen(body.position.x, body.position.y);
      ctx.save();
      ctx.translate(pos.x, pos.y);
      ctx.scale(this.cameraScale, this.cameraScale);
      ctx.rotate(body.angle || 0);

      for (let i = 0; i < cells.length; i++) {
        const data = p.cellData[i] || { cracks: [] };
        this.drawCellLocal(ctx, cells[i].x, cells[i].y, p, data);
      }
      this.drawPieceOuterBorder(ctx, p, cells);
      ctx.restore();
    }

    drawCellLocal(ctx, lx, ly, p, data) {
      const size = this.CELL * 1.035;
      ctx.save();
      ctx.translate(lx, ly);

      let fill = p.palette[0];
      let shadow = 'rgba(36, 67, 76, 0.18)';
      if (p.kind === 'quickFreeze') {
        fill = '#7ef4f3';
        shadow = 'rgba(0, 220, 230, 0.40)';
      } else if (p.kind === 'dirt') {
        fill = '#d7a63b';
        shadow = 'rgba(80, 48, 12, 0.22)';
      } else if (p.frozen) {
        fill = this.mixColor(p.palette[0], '#c9fbff', 0.55);
        shadow = 'rgba(153, 244, 255, 0.50)';
      }

      ctx.shadowColor = shadow;
      ctx.shadowBlur = p.frozen || p.kind === 'quickFreeze' ? 10 : 2;
      ctx.fillStyle = fill;
      ctx.strokeStyle = 'rgba(255,255,255,0.18)';
      ctx.lineWidth = p.frozen ? 1.3 : 0.7;
      this.roundRect(ctx, -size / 2, -size / 2, size, size, 4, true, true);
      ctx.shadowBlur = 0;

      // 非冻结方块的白框被刻意淡化；冻结后由整体外框统一加粗。
      if (p.kind !== 'dirt') {
        ctx.globalAlpha = p.frozen ? 0.54 : 0.20;
        ctx.fillStyle = '#ffffff';
        ctx.beginPath();
        ctx.moveTo(-size * 0.32, -size * 0.38);
        ctx.quadraticCurveTo(-size * 0.11, -size * 0.50, size * 0.22, -size * 0.35);
        ctx.quadraticCurveTo(size * 0.03, -size * 0.27, -size * 0.32, -size * 0.22);
        ctx.closePath();
        ctx.fill();
        ctx.globalAlpha = 1;
      }

      ctx.lineCap = 'round';
      ctx.lineJoin = 'round';
      ctx.strokeStyle = p.kind === 'dirt' ? '#8b6225' : (p.frozen ? '#efffff' : 'rgba(255,255,255,0.48)');
      ctx.lineWidth = p.frozen ? 2.4 : 1.15;
      for (const line of data.cracks) {
        ctx.beginPath();
        ctx.moveTo(line[0] * size, line[1] * size);
        for (let j = 2; j < line.length; j += 2) ctx.lineTo(line[j] * size, line[j + 1] * size);
        ctx.stroke();
      }

      if (p.kind === 'quickFreeze') {
        this.drawSnowBurst(ctx, 0, 0, size * 0.36);
      }
      if (p.frozen && p.kind !== 'dirt') {
        ctx.globalAlpha = 0.36;
        ctx.strokeStyle = '#bff8ff';
        ctx.lineWidth = 3.2;
        ctx.beginPath();
        ctx.moveTo(-size * 0.43, -size * 0.08);
        ctx.lineTo(size * 0.43, -size * 0.08);
        ctx.moveTo(-size * 0.16, -size * 0.43);
        ctx.lineTo(-size * 0.16, size * 0.43);
        ctx.stroke();
        ctx.globalAlpha = 1;
      }
      ctx.restore();
    }

    drawPieceOuterBorder(ctx, p, cells) {
      if (!cells || !cells.length) return;
      const shapeCells = p.shapeCells || cells.map((_, i) => [i, 0]);
      const has = new Set(shapeCells.map((c) => `${c[0]},${c[1]}`));
      const half = this.CELL * 0.515;
      ctx.save();
      ctx.lineCap = 'round';
      ctx.lineJoin = 'round';
      if (p.kind === 'dirt') {
        ctx.strokeStyle = '#f5df8e';
        ctx.lineWidth = 2.8;
      } else if (p.frozen || p.kind === 'quickFreeze') {
        ctx.strokeStyle = '#ffffff';
        ctx.lineWidth = 5.2;
        ctx.shadowColor = 'rgba(202, 255, 255, 0.72)';
        ctx.shadowBlur = 8;
      } else {
        ctx.strokeStyle = 'rgba(255,255,255,0.46)';
        ctx.lineWidth = 1.6;
      }

      for (let i = 0; i < cells.length; i++) {
        const c = cells[i];
        const g = shapeCells[i] || [i, 0];
        const gx = g[0];
        const gy = g[1];
        const x0 = c.x - half;
        const x1 = c.x + half;
        const y0 = c.y - half;
        const y1 = c.y + half;
        if (!has.has(`${gx},${gy - 1}`)) {
          ctx.beginPath(); ctx.moveTo(x0 + 3, y0); ctx.lineTo(x1 - 3, y0); ctx.stroke();
        }
        if (!has.has(`${gx},${gy + 1}`)) {
          ctx.beginPath(); ctx.moveTo(x0 + 3, y1); ctx.lineTo(x1 - 3, y1); ctx.stroke();
        }
        if (!has.has(`${gx - 1},${gy}`)) {
          ctx.beginPath(); ctx.moveTo(x0, y0 + 3); ctx.lineTo(x0, y1 - 3); ctx.stroke();
        }
        if (!has.has(`${gx + 1},${gy}`)) {
          ctx.beginPath(); ctx.moveTo(x1, y0 + 3); ctx.lineTo(x1, y1 - 3); ctx.stroke();
        }
      }

      if (p.frozen && p.kind !== 'dirt') {
        ctx.shadowBlur = 0;
        ctx.strokeStyle = '#bdf9ff';
        ctx.lineWidth = 2.1;
        for (let i = 0; i < cells.length; i++) {
          const c = cells[i];
          ctx.beginPath();
          ctx.moveTo(c.x - half * 0.62, c.y + half * 0.46);
          ctx.lineTo(c.x + half * 0.46, c.y - half * 0.62);
          ctx.stroke();
        }
      }
      ctx.restore();
    }

    drawSnowBurst(ctx, x, y, r) {
      ctx.save();
      ctx.translate(x, y);
      ctx.strokeStyle = '#ffffff';
      ctx.fillStyle = '#dfffff';
      ctx.lineWidth = 2.3;
      for (let i = 0; i < 8; i++) {
        const a = i * Math.PI / 4;
        ctx.beginPath();
        ctx.moveTo(Math.cos(a) * r * 0.25, Math.sin(a) * r * 0.25);
        ctx.lineTo(Math.cos(a) * r, Math.sin(a) * r);
        ctx.stroke();
      }
      ctx.beginPath();
      ctx.arc(0, 0, r * 0.28, 0, Math.PI * 2);
      ctx.fill();
      ctx.restore();
    }

    drawCart(ctx) {
      const pos = this.worldToScreen(this.cartX, this.cartY);
      const s = this.cameraScale;
      ctx.save();
      ctx.translate(pos.x, pos.y);
      ctx.scale(s, s);

      // 车厢木板
      ctx.fillStyle = '#4b3428';
      ctx.strokeStyle = '#241c19';
      ctx.lineWidth = 5;
      this.roundRect(ctx, -this.cartW / 2 - 12, -12, this.cartW + 24, 24, 7, true, true);
      ctx.fillStyle = '#5b3b2c';
      this.roundRect(ctx, -this.cartW / 2, -22, this.cartW, 18, 5, true, true);

      // 左右护栏/冰杖
      ctx.strokeStyle = '#2d201a';
      ctx.lineWidth = 7;
      ctx.beginPath();
      ctx.moveTo(-this.cartW / 2 + 10, -10);
      ctx.lineTo(-this.cartW / 2 + 10, -this.CART_WALL_H - 2);
      ctx.moveTo(this.cartW / 2 - 10, -10);
      ctx.lineTo(this.cartW / 2 - 10, -this.CART_WALL_H - 2);
      ctx.stroke();
      ctx.fillStyle = '#72f3ef';
      ctx.strokeStyle = '#f5ffff';
      ctx.lineWidth = 3;
      this.drawStar(ctx, -this.cartW / 2 + 10, -this.CART_WALL_H - 12, 14, 8);
      this.drawStar(ctx, this.cartW / 2 - 10, -this.CART_WALL_H - 12, 14, 8);

      // 积雪边
      ctx.fillStyle = '#f6ffff';
      ctx.beginPath();
      ctx.moveTo(-this.cartW / 2 - 8, -26);
      for (let x = -this.cartW / 2; x <= this.cartW / 2; x += 26) {
        ctx.quadraticCurveTo(x + 13, -18 + Math.sin(x * 0.06) * 3, x + 26, -26);
      }
      ctx.lineTo(this.cartW / 2 + 8, -14);
      ctx.lineTo(-this.cartW / 2 - 8, -14);
      ctx.closePath();
      ctx.fill();

      // 轮子
      const wheelY = 28;
      const wheelSpin = this.cartX * 0.035;
      this.drawWheel(ctx, -this.cartW * 0.24, wheelY, 24, wheelSpin);
      this.drawWheel(ctx, this.cartW * 0.24, wheelY, 24, wheelSpin);
      ctx.restore();
    }

    drawWheel(ctx, x, y, r, spin) {
      ctx.save();
      ctx.translate(x, y);
      ctx.rotate(spin);
      ctx.fillStyle = '#3a271f';
      ctx.strokeStyle = '#1e1714';
      ctx.lineWidth = 4;
      ctx.beginPath();
      ctx.arc(0, 0, r, 0, Math.PI * 2);
      ctx.fill();
      ctx.stroke();
      ctx.strokeStyle = '#c49a59';
      ctx.lineWidth = 4;
      for (let i = 0; i < 8; i++) {
        const a = i * Math.PI / 4;
        ctx.beginPath();
        ctx.moveTo(0, 0);
        ctx.lineTo(Math.cos(a) * r * 0.8, Math.sin(a) * r * 0.8);
        ctx.stroke();
      }
      ctx.fillStyle = '#8c5d2a';
      ctx.beginPath();
      ctx.arc(0, 0, 8, 0, Math.PI * 2);
      ctx.fill();
      ctx.restore();
    }

    drawFishGuard(ctx, wx, wy, dir) {
      const pos = this.worldToScreen(wx, wy);
      const s = this.cameraScale;
      ctx.save();
      ctx.translate(pos.x, pos.y);
      ctx.scale(s * dir, s);
      const bob = Math.sin(this.currentTime * 4 + wx * 0.01) * 2;
      ctx.translate(0, bob);
      ctx.lineWidth = 3;
      ctx.strokeStyle = '#342923';

      ctx.fillStyle = '#ecb23c';
      ctx.beginPath();
      ctx.ellipse(0, -38, 33, 39, -0.12, 0, Math.PI * 2);
      ctx.fill();
      ctx.stroke();
      ctx.fillStyle = '#c77c28';
      ctx.globalAlpha = 0.6;
      ctx.beginPath();
      ctx.ellipse(-10, -48, 8, 5, 0.4, 0, Math.PI * 2);
      ctx.ellipse(11, -62, 7, 4, -0.2, 0, Math.PI * 2);
      ctx.ellipse(8, -26, 9, 5, 0.1, 0, Math.PI * 2);
      ctx.fill();
      ctx.globalAlpha = 1;

      ctx.fillStyle = '#dfe6b7';
      ctx.strokeStyle = '#30515b';
      ctx.lineWidth = 5;
      ctx.beginPath();
      ctx.ellipse(10, -36, 23, 20, -0.05, 0, Math.PI * 2);
      ctx.fill();
      ctx.stroke();
      ctx.strokeStyle = '#342923';
      ctx.lineWidth = 2;
      ctx.beginPath();
      ctx.arc(4, -54, 7, 0, Math.PI * 2);
      ctx.fillStyle = '#f6f4cf';
      ctx.fill();
      ctx.stroke();
      ctx.fillStyle = '#2d2624';
      ctx.beginPath();
      ctx.arc(5, -54, 2.8, 0, Math.PI * 2);
      ctx.fill();

      ctx.fillStyle = '#e8e2c8';
      ctx.strokeStyle = '#342923';
      ctx.lineWidth = 3;
      this.roundRect(ctx, -18, 0, 28, 38, 5, true, true);
      ctx.fillStyle = '#bccfbe';
      ctx.beginPath();
      ctx.ellipse(-28, 0, 10, 16, 0.4, 0, Math.PI * 2);
      ctx.fill();
      ctx.stroke();
      ctx.restore();
    }

    drawEffects(ctx) {
      for (const e of this.effects) {
        const t = e.t / e.life;
        const pos = this.worldToScreen(e.x, e.y);
        ctx.save();
        ctx.globalAlpha = Math.max(0, 1 - t);
        if (e.type === 'freeze' || e.type === 'quickFreeze' || e.type === 'cartFreeze') {
          ctx.strokeStyle = e.type === 'quickFreeze' ? '#eaffff' : '#dfffff';
          ctx.lineWidth = 3;
          ctx.beginPath();
          ctx.arc(pos.x, pos.y, (18 + 46 * t) * this.cameraScale, 0, Math.PI * 2);
          ctx.stroke();
          for (let i = 0; i < 10; i++) {
            const a = i * Math.PI * 0.2 + t * 2;
            const r = (12 + 38 * t) * this.cameraScale;
            this.drawStar(ctx, pos.x + Math.cos(a) * r, pos.y + Math.sin(a) * r, 4 * this.cameraScale, 5);
          }
        } else if (e.type === 'miss') {
          ctx.fillStyle = '#fff1c8';
          ctx.font = `bold ${26 * this.cameraScale}px KaiTi, STKaiti, serif`;
          ctx.textAlign = 'center';
          ctx.fillText('掉落！', pos.x, pos.y - 30 * t);
        } else if (e.type === 'rotate') {
          ctx.strokeStyle = '#fff7c9';
          ctx.lineWidth = 3;
          ctx.beginPath();
          ctx.arc(pos.x, pos.y, (24 + 14 * t) * this.cameraScale, -1, Math.PI * 1.4);
          ctx.stroke();
        } else if (e.type === 'spawn') {
          ctx.strokeStyle = 'rgba(255,255,255,0.75)';
          ctx.lineWidth = 2;
          ctx.beginPath();
          ctx.moveTo(pos.x, 0);
          ctx.lineTo(pos.x, pos.y - 18 * this.cameraScale);
          ctx.stroke();
        }
        ctx.restore();
      }
    }

    drawUI(ctx) {
      const buttons = this.getButtons();
      this.drawTopInfo(ctx);
      this.drawButton(ctx, buttons.drop, '下落', this.dropHeld);
      this.drawScorePlate(ctx, buttons.score);
      this.drawButton(ctx, buttons.rotate, '旋转', false);
    }

    drawTopInfo(ctx) {
      ctx.save();
      ctx.textAlign = 'right';
      ctx.font = 'bold 18px KaiTi, STKaiti, Songti SC, serif';
      ctx.fillStyle = 'rgba(251, 226, 160, 0.88)';
      this.roundRect(ctx, this.W - 96, 18, 80, 32, 3, true, false);
      ctx.fillStyle = '#3d2b24';
      ctx.fillText(`漏 ${this.missedPieces}/${this.MISS_LIMIT}`, this.W - 28, 40);

      ctx.textAlign = 'center';
      ctx.fillStyle = '#f5e0b4';
      ctx.strokeStyle = '#2c251f';
      ctx.lineWidth = 2;
      ctx.beginPath();
      ctx.arc(this.W - 44, 78, 22, 0, Math.PI * 2);
      ctx.fill();
      ctx.stroke();
      ctx.strokeStyle = '#2c251f';
      ctx.lineWidth = 4;
      ctx.beginPath();
      ctx.moveTo(this.W - 53, 69);
      ctx.lineTo(this.W - 35, 87);
      ctx.moveTo(this.W - 35, 69);
      ctx.lineTo(this.W - 53, 87);
      ctx.stroke();
      ctx.restore();
    }

    getButtons() {
      const bottomSafe = 18;
      const y = this.H - 75 - bottomSafe;
      const h = 58;
      const sideW = Math.max(96, Math.min(128, this.W * 0.28));
      const centerW = Math.max(126, Math.min(178, this.W * 0.38));
      return {
        drop: { x: 14, y, w: sideW, h },
        score: { x: (this.W - centerW) / 2, y: y - 4, w: centerW, h: h + 8 },
        rotate: { x: this.W - sideW - 14, y, w: sideW, h }
      };
    }

    getRestartButton() {
      return { x: this.W / 2 - 82, y: this.H / 2 + 42, w: 164, h: 52 };
    }

    drawButton(ctx, r, text, pressed) {
      ctx.save();
      ctx.translate(0, pressed ? 3 : 0);
      ctx.fillStyle = pressed ? '#d8be83' : '#f1dba4';
      ctx.strokeStyle = '#65472d';
      ctx.lineWidth = 4;
      this.roundRect(ctx, r.x, r.y, r.w, r.h, 9, true, true);
      ctx.strokeStyle = 'rgba(255,255,255,0.46)';
      ctx.lineWidth = 2;
      this.roundRect(ctx, r.x + 6, r.y + 6, r.w - 12, r.h - 12, 6, false, true);
      ctx.fillStyle = '#5b3b25';
      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      ctx.font = `bold ${Math.min(30, r.h * 0.47)}px KaiTi, STKaiti, Songti SC, serif`;
      ctx.fillText(text, r.x + r.w / 2, r.y + r.h / 2 + 1);
      ctx.restore();
    }

    drawScorePlate(ctx, r) {
      ctx.save();
      ctx.fillStyle = '#5a3a28';
      ctx.strokeStyle = '#2d211b';
      ctx.lineWidth = 5;
      this.roundRect(ctx, r.x, r.y, r.w, r.h, 8, true, true);
      ctx.strokeStyle = '#8b6d46';
      ctx.lineWidth = 2;
      this.roundRect(ctx, r.x + 6, r.y + 6, r.w - 12, r.h - 12, 5, false, true);
      ctx.fillStyle = '#f5e7bf';
      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      ctx.font = `bold ${Math.min(24, r.h * 0.34)}px KaiTi, STKaiti, Songti SC, serif`;
      ctx.fillText(`装载${this.loadedCells}块冰块`, r.x + r.w / 2, r.y + r.h / 2 + 1);
      ctx.restore();
    }

    drawGameOver(ctx) {
      ctx.save();
      ctx.fillStyle = 'rgba(24, 42, 48, 0.62)';
      ctx.fillRect(0, 0, this.W, this.H);
      ctx.fillStyle = '#f4e6c7';
      ctx.strokeStyle = '#332822';
      ctx.lineWidth = 5;
      this.roundRect(ctx, this.W / 2 - 138, this.H / 2 - 112, 276, 224, 14, true, true);
      ctx.fillStyle = '#453126';
      ctx.textAlign = 'center';
      ctx.font = 'bold 34px KaiTi, STKaiti, serif';
      ctx.fillText('游戏结束', this.W / 2, this.H / 2 - 54);
      ctx.font = '22px KaiTi, STKaiti, serif';
      ctx.fillText(`最终装载：${this.loadedCells} 块`, this.W / 2, this.H / 2 - 12);
      const b = this.getRestartButton();
      this.drawButton(ctx, b, '再来一局', false);
      ctx.restore();
    }

    // ====== 小工具 ======
    weightedChoice(arr) {
      const sum = arr.reduce((acc, x) => acc + x.weight, 0);
      let r = Math.random() * sum;
      for (const x of arr) {
        r -= x.weight;
        if (r <= 0) return x;
      }
      return arr[arr.length - 1];
    }

    makeCracks(seed) {
      const rand = this.seeded(seed);
      const count = 2 + Math.floor(rand() * 3);
      const lines = [];
      for (let i = 0; i < count; i++) {
        const sx = rand() * 0.7 - 0.35;
        const sy = rand() * 0.7 - 0.35;
        const ex = sx + rand() * 0.5 - 0.25;
        const ey = sy + rand() * 0.5 - 0.25;
        const mx = (sx + ex) / 2 + rand() * 0.16 - 0.08;
        const my = (sy + ey) / 2 + rand() * 0.16 - 0.08;
        lines.push([sx, sy, mx, my, ex, ey]);
      }
      return lines;
    }

    seeded(seed) {
      let s = Math.sin(seed) * 10000;
      return function () {
        s = Math.sin(s) * 10000;
        return s - Math.floor(s);
      };
    }

    random(a, b) {
      return a + Math.random() * (b - a);
    }

    clamp(v, a, b) {
      return Math.max(a, Math.min(b, v));
    }

    pointInRect(p, r) {
      return p.x >= r.x && p.x <= r.x + r.w && p.y >= r.y && p.y <= r.y + r.h;
    }

    roundRect(ctx, x, y, w, h, r, fill, stroke) {
      r = Math.min(r, w / 2, h / 2);
      ctx.beginPath();
      ctx.moveTo(x + r, y);
      ctx.lineTo(x + w - r, y);
      ctx.quadraticCurveTo(x + w, y, x + w, y + r);
      ctx.lineTo(x + w, y + h - r);
      ctx.quadraticCurveTo(x + w, y + h, x + w - r, y + h);
      ctx.lineTo(x + r, y + h);
      ctx.quadraticCurveTo(x, y + h, x, y + h - r);
      ctx.lineTo(x, y + r);
      ctx.quadraticCurveTo(x, y, x + r, y);
      ctx.closePath();
      if (fill) ctx.fill();
      if (stroke) ctx.stroke();
    }

    drawHeart(ctx, x, y, s) {
      ctx.save();
      ctx.translate(x, y);
      ctx.scale(s / 16, s / 16);
      ctx.beginPath();
      ctx.moveTo(0, 6);
      ctx.bezierCurveTo(-12, -4, -7, -14, 0, -8);
      ctx.bezierCurveTo(7, -14, 12, -4, 0, 6);
      ctx.fill();
      ctx.restore();
    }

    drawStar(ctx, x, y, r, points) {
      ctx.save();
      ctx.translate(x, y);
      ctx.beginPath();
      for (let i = 0; i < points * 2; i++) {
        const a = -Math.PI / 2 + i * Math.PI / points;
        const rr = i % 2 === 0 ? r : r * 0.46;
        const px = Math.cos(a) * rr;
        const py = Math.sin(a) * rr;
        if (i === 0) ctx.moveTo(px, py); else ctx.lineTo(px, py);
      }
      ctx.closePath();
      ctx.fill();
      ctx.stroke();
      ctx.restore();
    }

    mixColor(a, b, t) {
      const ca = this.hexToRgb(a);
      const cb = this.hexToRgb(b);
      const r = Math.round(ca.r + (cb.r - ca.r) * t);
      const g = Math.round(ca.g + (cb.g - ca.g) * t);
      const bl = Math.round(ca.b + (cb.b - ca.b) * t);
      return `rgb(${r},${g},${bl})`;
    }

    hexToRgb(hex) {
      const h = hex.replace('#', '');
      const n = parseInt(h.length === 3 ? h.split('').map(c => c + c).join('') : h, 16);
      return { r: (n >> 16) & 255, g: (n >> 8) & 255, b: n & 255 };
    }
  }
})();
