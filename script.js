/* =====================================================================
   Gothic Remake Lockpick Solver
   Cała logika aplikacji: solver (przepisany z R) + obsługa interfejsu.
   Aplikacja jest w pełni statyczna — brak backendu, brak buildu.
   ===================================================================== */

/* =====================================================================
   1. ARYTMETYKA UŁAMKÓW (odpowiednik MASS::fractions z R)
   Solver rozwiązuje układ równań dokładnie, na ułamkach, aby uniknąć
   błędów zaokrągleń liczb zmiennoprzecinkowych.
   ===================================================================== */

function gcd(a, b) {
  a = Math.abs(a);
  b = Math.abs(b);
  while (b) { [a, b] = [b, a % b]; }
  return a || 1;
}

function lcm(a, b) {
  return Math.abs(a * b) / gcd(a, b);
}

class Frac {
  constructor(n, d = 1) {
    if (d === 0) throw new Error('Dzielenie przez zero we frakcji.');
    if (d < 0) { n = -n; d = -d; }
    const g = gcd(n, d);
    this.n = g === 0 ? 0 : n / g;
    this.d = g === 0 ? 1 : d / g;
  }
  add(o) { return new Frac(this.n * o.d + o.n * this.d, this.d * o.d); }
  sub(o) { return new Frac(this.n * o.d - o.n * this.d, this.d * o.d); }
  mul(o) { return new Frac(this.n * o.n, this.d * o.d); }
  div(o) { return new Frac(this.n * o.d, this.d * o.n); }
  isZero() { return this.n === 0; }
  toNumber() { return this.n / this.d; }
}

function transpose(matrix) {
  const rows = matrix.length;
  const cols = matrix[0].length;
  const result = [];
  for (let c = 0; c < cols; c++) {
    result.push([]);
    for (let r = 0; r < rows; r++) result[c].push(matrix[r][c]);
  }
  return result;
}

/**
 * Rozwiązuje układ równań M * x = b metodą eliminacji Gaussa-Jordana,
 * z dokładną arytmetyką ułamków (odpowiednik solve() w R).
 * Zwraca tablicę obiektów Frac.
 */
function solveLinearSystem(M, b) {
  const n = M.length;
  const A = M.map((row, i) => row.map((v) => new Frac(v)).concat([new Frac(b[i])]));

  for (let col = 0; col < n; col++) {
    let pivotRow = -1;
    for (let r = col; r < n; r++) {
      if (!A[r][col].isZero()) { pivotRow = r; break; }
    }
    if (pivotRow === -1) {
      throw new Error('Układ równań nie ma jednoznacznego rozwiązania dla podanej konfiguracji.');
    }
    [A[col], A[pivotRow]] = [A[pivotRow], A[col]];

    const pivotVal = A[col][col];
    for (let c = col; c <= n; c++) A[col][c] = A[col][c].div(pivotVal);

    for (let r = 0; r < n; r++) {
      if (r === col) continue;
      const factor = A[r][col];
      if (factor.isZero()) continue;
      for (let c = col; c <= n; c++) A[r][c] = A[r][c].sub(factor.mul(A[col][c]));
    }
  }

  return A.map((row) => row[n]);
}

/* =====================================================================
   2. MOVESET — tabela ruchów per liczba bloczków
   Moveset jest teraz w pełni edytowalny przez użytkownika (klik na komórkę
   w panelu "Moveset" cyklicznie zmienia wartość -1 -> 0 -> 1 -> -1).
   Wiersze = BlockID (B1..BN), kolumny = wpływ ruchu na pozycję Block1..BlockN.

   Domyślny punkt startowy dla 6 bloczków to oryginalne dane z gry
   (DEFAULT_MOVESET_6) — użytkownik może je dalej edytować. Dla innych
   rozmiarów startujemy od macierzy jednostkowej (każdy bloczek wpływa
   tylko sam na siebie), również w pełni edytowalnej.
   ===================================================================== */

const DEFAULT_MOVESET_6 = [
  [1, 0, 0, 0, 0, 0],
  [0, 1, 0, 0, 0, 0],
  [0, 0, 1, 0, 0, 0],
  [0, 0, 0, 1, 0, 0],
  [0, 0, 0, 0, 1, 0],
  [0, 0, 0, 0, 0, 1],
];

function identityMoveset(n) {
  const m = [];
  for (let i = 0; i < n; i++) {
    const row = new Array(n).fill(0);
    row[i] = 1;
    m.push(row);
  }
  return m;
}

/**
 * Buduje macierz startową dla danej liczby bloczków (użyte tylko przy
 * pierwszym wejściu w dany rozmiar — potem macierz jest już "tknięta"
 * przez użytkownika i resize zachowuje jego wartości, patrz resizeMoveset).
 */
function defaultMovesetFor(n) {
  return n === 6 ? DEFAULT_MOVESET_6.map((row) => row.slice()) : identityMoveset(n);
}

/**
 * Przycina lub rozszerza istniejącą macierz do nowego rozmiaru n,
 * zachowując wartości komórek, które mieszczą się w nowym rozmiarze.
 * Nowo dodane komórki na przekątnej dostają 1 (jak w macierzy jednostkowej),
 * pozostałe nowo dodane komórki dostają 0.
 */
function resizeMoveset(oldMatrix, n) {
  const result = [];
  for (let i = 0; i < n; i++) {
    const row = new Array(n).fill(0);
    for (let j = 0; j < n; j++) {
      if (oldMatrix[i] && oldMatrix[i][j] !== undefined) {
        row[j] = oldMatrix[i][j];
      } else if (i === j) {
        row[j] = 1;
      }
    }
    result.push(row);
  }
  return result;
}

/** Cykl edycji pojedynczej komórki: -1 -> 0 -> 1 -> -1 */
function nextMovesetValue(v) {
  if (v === -1) return 0;
  if (v === 0) return 1;
  return -1;
}

/* =====================================================================
   3. SOLVER — pełna logika przepisana z R
   Kroki (identyczne jak w oryginale):
     1) centrowanie pozycji startowej (pin 4 = 0),
     2) rozwiązanie układu t(A) * x = b,
     3) sprowadzenie x do wspólnego mianownika (LCM) -> liczby ruchów,
     4) kolejność bloczków wg sumy |wpływów| (rosnąco, potem alfabetycznie),
     5) symulacja ruchów z omijaniem zakazanych pozycji (poza zakresem -3..3),
     6) kompresja powtarzających się ruchów (rle).

   Uwaga do portu: oryginalny kod R liczący LCM ma błąd zasięgu zmiennych
   (przy 1 lub 2 unikalnych mianownikach `actual_lcm` nigdy nie zostaje
   ustawiony w pętli). Poniżej zaimplementowano zamierzoną logikę — LCM
   wszystkich unikalnych mianowników — bez zmiany właściwej matematyki
   algorytmu.
   ===================================================================== */

function solveLockpick(startingPositions, movesetMatrix) {
  const n = startingPositions.length;

  // 1) centrowanie: pin 4 -> 0
  const centralized = startingPositions.map((v) => v - 4);
  const targetB = centralized.map((v) => -v);

  // 2) rozwiązanie układu t(A) * x = b
  const At = transpose(movesetMatrix);
  const x = solveLinearSystem(At, targetB);

  // 3) LCM mianowników -> skalowanie do liczby całkowitej ruchów
  const denominators = [...new Set(x.filter((f) => f.d !== 1).map((f) => f.d))];
  const actualLcm = denominators.length === 0
    ? 1
    : denominators.reduce((acc, d) => lcm(acc, d), denominators[0]);

  const solution = x.map((f) => Math.round(f.mul(new Frac(actualLcm)).toNumber()));

  // 4) kolejność bloczków: rosnąco wg sumy |wartości| w wierszu moveset, potem alfabetycznie
  const activeBlocks = solution
    .map((reps, idx) => ({ id: `B${idx + 1}`, idx, reps }))
    .filter((b) => b.reps !== 0);

  if (activeBlocks.length === 0) {
    // Pozycja startowa już jest rozwiązaniem — brak ruchów do wykonania.
    return { rle: [], finalPosition: centralized, movesCount: 0 };
  }

  const withSumAbs = activeBlocks.map((b) => ({
    ...b,
    sumAbs: movesetMatrix[b.idx].reduce((s, v) => s + Math.abs(v), 0),
  }));
  withSumAbs.sort((a, b) => a.sumAbs - b.sumAbs || a.id.localeCompare(b.id));

  // budowa listy pojedynczych ruchów w kolejności bloczków
  let allMoves = [];
  for (const b of withSumAbs) {
    const dir = b.reps > 0 ? 'L' : 'R';
    for (let i = 0; i < Math.abs(b.reps); i++) {
      allMoves.push({ block: b.id, idx: b.idx, dir });
    }
  }

  // 5) symulacja z omijaniem zakazanych pozycji (kolejka: nieudany ruch wraca na koniec)
  let queue = allMoves.slice();
  let position = centralized.slice();
  const acceptedMoves = [];
  let guard = 0;
  const guardLimit = Math.max(5000, allMoves.length * allMoves.length * 4);

  while (queue.length > 0) {
    guard += 1;
    if (guard > guardLimit) {
      throw new Error('Solver nie znalazł prawidłowej kolejności ruchów (zbyt wiele prób).');
    }
    const move = queue[0];
    const vec = movesetMatrix[move.idx];
    const effect = move.dir === 'R' ? vec.map((v) => -v) : vec;
    const next = position.map((v, i) => v + effect[i]);
    const prohibited = next.some((v) => v > 3 || v < -3);

    if (!prohibited) {
      acceptedMoves.push(move);
      position = next;
      queue.shift();
    } else {
      queue.push(queue.shift());
    }
  }

  // 6) kompresja powtarzających się ruchów (rle)
  const rle = [];
  for (const m of acceptedMoves) {
    const last = rle[rle.length - 1];
    if (last && last.block === m.block && last.dir === m.dir) {
      last.count += 1;
    } else {
      rle.push({ block: m.block, dir: m.dir, count: 1 });
    }
  }

  return { rle, finalPosition: position, movesCount: acceptedMoves.length };
}

/* =====================================================================
   4. STAN APLIKACJI
   ===================================================================== */

const state = {
  blockCount: 6,
  selections: new Array(6).fill(null), // pozycja startowa (1-7) dla każdego bloczka lub null
  movesetMatrix: defaultMovesetFor(6), // edytowalna macierz moveset dla obecnej liczby bloczków
  mobilePanel: 'starting', // 'starting' | 'moveset'
  mode: 'blocks', // 'blocks' | 'arrows'
  result: null, // wynik ostatniego solve()
};

/* =====================================================================
   5. REFERENCJE DOM
   ===================================================================== */

const el = {
  blockCountSlider: document.getElementById('blockCountSlider'),
  blockCountValue: document.getElementById('blockCountValue'),
  pinGrid: document.getElementById('pinGrid'),
  solveBtn: document.getElementById('solveBtn'),
  solveWarning: document.getElementById('solveWarning'),
  movesetTable: document.getElementById('movesetTable'),
  movesetWarning: document.getElementById('movesetWarning'),
  solutionContent: document.getElementById('solutionContent'),
  solutionActions: document.getElementById('solutionActions'),
  modeSwitch: document.getElementById('modeSwitch'),
  modeToggle: document.getElementById('modeToggle'),
  copyBtn: document.getElementById('copyBtn'),
  resetBtn: document.getElementById('resetBtn'),
  mobileSwitch: document.getElementById('mobileSwitch'),
  mobileSwitchTrack: document.getElementById('mobileSwitchTrack'),
  startingPanel: document.getElementById('startingPanel'),
  movesetPanel: document.getElementById('movesetPanel'),
};

/* =====================================================================
   6. RENDEROWANIE: panel "Starting position" (siatka pinów)
   ===================================================================== */

function renderPinGrid() {
  const n = state.blockCount;
  el.pinGrid.innerHTML = '';

  // nagłówek kolumn (numery pinów 1-7)
  const header = document.createElement('div');
  header.className = 'pin-grid-header';
  const cornerCell = document.createElement('div');
  header.appendChild(cornerCell);
  for (let p = 1; p <= 7; p++) {
    const cell = document.createElement('div');
    cell.className = 'pin-grid-header-cell';
    cell.textContent = String(p);
    header.appendChild(cell);
  }
  el.pinGrid.appendChild(header);

  // wiersze bloczków: od najwyższego (BN) na górze, do B1 na dole
  for (let blockNum = n; blockNum >= 1; blockNum--) {
    const row = document.createElement('div');
    row.className = 'pin-row';

    const label = document.createElement('div');
    label.className = 'pin-row-label';
    label.textContent = `B${blockNum}`;
    row.appendChild(label);

    for (let pin = 1; pin <= 7; pin++) {
      const hit = document.createElement('button');
      hit.type = 'button';
      hit.className = 'pin-hit';
      hit.dataset.block = String(blockNum);
      hit.dataset.pin = String(pin);
      hit.setAttribute('aria-label', `Bloczek B${blockNum}, pin ${pin}`);

      const visual = document.createElement('span');
      visual.className = 'pin-visual';
      if (pin === 4) visual.classList.add('is-center');
      if (state.selections[blockNum - 1] === pin) visual.classList.add('is-selected');

      hit.appendChild(visual);
      hit.addEventListener('click', () => selectPin(blockNum, pin));
      row.appendChild(hit);
    }

    el.pinGrid.appendChild(row);
  }
}

function selectPin(blockNum, pin) {
  state.selections[blockNum - 1] = pin;
  renderPinGrid();
  clearSolveWarning();
}

/* =====================================================================
   7. RENDEROWANIE: panel "Moveset" (tabela techniczna)
   ===================================================================== */

function symbolForValue(v) {
  if (v === 1) return 'S';
  if (v === -1) return 'O';
  return '-';
}

function handleMovesetCellClick(i, j) {
  const matrix = state.movesetMatrix;
  matrix[i][j] = nextMovesetValue(matrix[i][j]);
  renderMovesetTable();
  clearSolution();
}

function renderMovesetTable() {
  const n = state.blockCount;
  const matrix = state.movesetMatrix;

  el.movesetWarning.hidden = false;
  el.movesetWarning.textContent = 'Kliknij komórkę, aby zmienić jej wartość (-1 → 0 → 1 → -1).';

  el.movesetTable.innerHTML = '';

  const thead = document.createElement('thead');
  const headRow = document.createElement('tr');
  headRow.appendChild(document.createElement('th'));
  for (let p = 1; p <= n; p++) {
    const th = document.createElement('th');
    th.textContent = String(p);
    headRow.appendChild(th);
  }
  thead.appendChild(headRow);
  el.movesetTable.appendChild(thead);

  const tbody = document.createElement('tbody');
  for (let i = 0; i < n; i++) {
    const tr = document.createElement('tr');
    const th = document.createElement('th');
    th.textContent = `B${i + 1}`;
    tr.appendChild(th);

    for (let j = 0; j < n; j++) {
      const td = document.createElement('td');
      td.className = 'moveset-cell';
      td.setAttribute('role', 'button');
      td.tabIndex = 0;
      td.setAttribute('aria-label', `B${i + 1}, kolumna ${j + 1}`);
      const v = matrix[i][j];
      td.textContent = symbolForValue(v);
      if (v === 1) td.classList.add('val-pos');
      if (v === -1) td.classList.add('val-neg');
      td.addEventListener('click', () => handleMovesetCellClick(i, j));
      td.addEventListener('keydown', (e) => {
        if (e.key === 'Enter' || e.key === ' ') {
          e.preventDefault();
          handleMovesetCellClick(i, j);
        }
      });
      tr.appendChild(td);
    }
    tbody.appendChild(tr);
  }
  el.movesetTable.appendChild(tbody);
}

/* =====================================================================
   8. OBSŁUGA: liczba bloczków
   ===================================================================== */

function handleBlockCountChange() {
  const n = parseInt(el.blockCountSlider.value, 10);
  state.blockCount = n;
  state.selections = new Array(n).fill(null);
  state.movesetMatrix = resizeMoveset(state.movesetMatrix, n);
  el.blockCountValue.textContent = String(n);
  renderPinGrid();
  renderMovesetTable();
  clearSolution();
  clearSolveWarning();
}

/* =====================================================================
   9. OBSŁUGA: SOLVE
   ===================================================================== */

function clearSolveWarning() {
  el.solveBtn.classList.remove('is-error');
  el.solveWarning.hidden = true;
}

function handleSolve() {
  const hasEmpty = state.selections.some((v) => v === null);
  if (hasEmpty) {
    el.solveBtn.classList.add('is-error');
    el.solveWarning.hidden = false;
    return;
  }
  clearSolveWarning();

  try {
    const result = solveLockpick(state.selections.slice(), state.movesetMatrix);
    state.result = result;
    renderSolution();
  } catch (err) {
    state.result = null;
    el.modeSwitch.hidden = true;
    el.solutionActions.hidden = true;
    el.solutionContent.innerHTML = '';
    const p = document.createElement('p');
    p.className = 'solution-error';
    p.textContent = err.message || 'Nie udało się wyznaczyć rozwiązania.';
    el.solutionContent.appendChild(p);
  }
}

/* =====================================================================
   10. RENDEROWANIE: panel Solution (Blocks / Arrows)
   ===================================================================== */

function dirArrow(dir) {
  return dir === 'L' ? '←' : '→';
}

function renderBlocksMode(rle) {
  const ul = document.createElement('ul');
  ul.className = 'solution-lines';
  for (const step of rle) {
    const li = document.createElement('li');
    const block = document.createElement('span');
    block.className = 'move-block';
    block.textContent = step.block;
    const dir = document.createElement('span');
    dir.className = 'move-dir';
    dir.textContent = dirArrow(step.dir);
    const count = document.createElement('span');
    count.className = 'move-count';
    count.textContent = `×${step.count}`;
    li.appendChild(block);
    li.appendChild(dir);
    li.appendChild(count);
    ul.appendChild(li);
  }
  return ul;
}

function renderArrowsMode(rle) {
  // Start zawsze z bloczka B1. ↑/↓ zmienia aktywny bloczek, ←/→ wykonuje ruch.
  const tokens = [];
  let current = 1;

  for (const step of rle) {
    const target = parseInt(step.block.slice(1), 10);
    const diff = target - current;
    if (diff > 0) tokens.push({ symbol: '↑', count: diff });
    else if (diff < 0) tokens.push({ symbol: '↓', count: -diff });
    current = target;

    tokens.push({ symbol: dirArrow(step.dir), count: step.count });
  }

  // kompresja sąsiadujących identycznych symboli (na wypadek kolejnych po sobie)
  const compressed = [];
  for (const t of tokens) {
    const last = compressed[compressed.length - 1];
    if (last && last.symbol === t.symbol) last.count += t.count;
    else compressed.push({ ...t });
  }

  const p = document.createElement('p');
  p.className = 'solution-arrows';
  p.innerHTML = compressed
    .map((t) => `<span class="step">${t.symbol}${t.count > 1 ? `x${t.count}` : ''}</span>`)
    .join(' ');
  return p;
}

function renderSolution() {
  const result = state.result;
  if (!result) return;

  el.modeSwitch.hidden = false;
  el.solutionActions.hidden = false;
  el.solutionContent.innerHTML = '';

  if (result.rle.length === 0) {
    const p = document.createElement('p');
    p.className = 'solution-placeholder';
    p.textContent = 'Pozycja startowa jest już rozwiązaniem — brak ruchów do wykonania.';
    el.solutionContent.appendChild(p);
    return;
  }

  const node = state.mode === 'blocks'
    ? renderBlocksMode(result.rle)
    : renderArrowsMode(result.rle);
  el.solutionContent.appendChild(node);

  updateModeSwitchUI();
}

function updateModeSwitchUI() {
  el.modeToggle.dataset.mode = state.mode;
  el.modeSwitch.querySelectorAll('[data-mode-label]').forEach((elem) => {
    elem.dataset.active = String(elem.dataset.modeLabel === state.mode);
  });
}

function toggleMode() {
  state.mode = state.mode === 'blocks' ? 'arrows' : 'blocks';
  renderSolution();
}

/* =====================================================================
   11. COPY / RESET
   ===================================================================== */

function getSolutionText() {
  const result = state.result;
  if (!result || result.rle.length === 0) return '';

  if (state.mode === 'blocks') {
    return result.rle.map((s) => `${s.block} ${dirArrow(s.dir)} ×${s.count}`).join('\n');
  }

  let current = 1;
  const parts = [];
  for (const step of result.rle) {
    const target = parseInt(step.block.slice(1), 10);
    const diff = target - current;
    if (diff > 0) parts.push(`↑${diff > 1 ? `x${diff}` : ''}`);
    else if (diff < 0) parts.push(`↓${-diff > 1 ? `x${-diff}` : ''}`);
    current = target;
    const arrow = dirArrow(step.dir);
    parts.push(`${arrow}${step.count > 1 ? `x${step.count}` : ''}`);
  }
  return parts.join(' ');
}

async function handleCopy() {
  const text = getSolutionText();
  if (!text) return;
  try {
    await navigator.clipboard.writeText(text);
  } catch (err) {
    // Fallback dla środowisk bez dostępu do clipboard API
    const textarea = document.createElement('textarea');
    textarea.value = text;
    textarea.style.position = 'fixed';
    textarea.style.opacity = '0';
    document.body.appendChild(textarea);
    textarea.select();
    document.execCommand('copy');
    document.body.removeChild(textarea);
  }
}

function clearSolution() {
  state.result = null;
  el.modeSwitch.hidden = true;
  el.solutionActions.hidden = true;
  el.solutionContent.innerHTML = '<p class="solution-placeholder">Enter data and press solve</p>';
}

function handleReset() {
  state.blockCount = 4;
  state.selections = new Array(4).fill(null);
  state.movesetMatrix = defaultMovesetFor(4);
  state.mode = 'blocks';
  el.blockCountSlider.value = '4';
  el.blockCountValue.textContent = '4';
  renderPinGrid();
  renderMovesetTable();
  clearSolution();
  clearSolveWarning();
  updateModeSwitchUI();
}

/* =====================================================================
   12. PRZEŁĄCZNIK MOBILNY (Starting position <-> Moveset)
   ===================================================================== */

function setMobilePanel(target) {
  state.mobilePanel = target;
  el.startingPanel.classList.toggle('is-active-mobile', target === 'starting');
  el.movesetPanel.classList.toggle('is-active-mobile', target === 'moveset');

  el.mobileSwitch.querySelectorAll('.mobile-switch-option').forEach((btn) => {
    btn.classList.toggle('is-active', btn.dataset.target === target);
  });
  el.mobileSwitchTrack.classList.toggle('is-right', target === 'moveset');
}

/* =====================================================================
   13. INICJALIZACJA
   ===================================================================== */

function init() {
  renderPinGrid();
  renderMovesetTable();
  updateModeSwitchUI();

  el.blockCountSlider.addEventListener('input', handleBlockCountChange);
  el.solveBtn.addEventListener('click', handleSolve);
  el.modeToggle.addEventListener('click', toggleMode);
  el.copyBtn.addEventListener('click', handleCopy);
  el.resetBtn.addEventListener('click', handleReset);

  el.mobileSwitch.querySelectorAll('.mobile-switch-option').forEach((btn) => {
    btn.addEventListener('click', () => setMobilePanel(btn.dataset.target));
  });
  el.mobileSwitchTrack.addEventListener('click', () => {
    setMobilePanel(state.mobilePanel === 'starting' ? 'moveset' : 'starting');
  });
}

document.addEventListener('DOMContentLoaded', init);
