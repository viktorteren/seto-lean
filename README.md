# seto-lean

Decomposizione di dimostrazioni **Lean 4** in **State Machines** tramite **[Seto 2.0](https://github.com/viktorteren/Seto)** con visualizzazione interattiva HTML/SVG.

## Funzionalità
- **Parser Lean 4** (`lean_to_sm.py`): estrae blocchi `theorem` / `lemma` / `def ... := by` e modella rami (`| ... =>`, `case`, `have ... := by`) e sequenze di tattiche come Transition System (`.g`).
- **Decomposizione con Seto 2.0**: esegue `Seto` in modalità isolata (`SM O --work-dir=...`) estraendo le State Machine interagenti.
- **Visualizzazione HTML/SVG interattiva** (zero dipendenze esterne, apribile nel browser):
  - **Layout verticale (top-down)** con viste **Colonne affiancate** o **Impilate**;
  - **Raggruppamento automatico** dei blocchi lineari di tattiche consecutive;
  - **Pan & Zoom** (rotellina, drag, `+`/`−`/`Fit`/`100%`/`⛶`);
  - **Evidenziazione sincronizzazioni cross-SM**: cliccando una tattica si illuminano tutte le sue ricorrenze in tutte le SM e si evidenzia la riga esatta nel codice `.lean`.

## Dipendenze (`Seto 2.0` come git submodule)
`deps/Seto` punta a `https://github.com/viktorteren/Seto.git`:
```bash
git clone --recursive https://github.com/viktorteren/seto-lean.git
cd seto-lean
```
Compila `Seto` (C++20, CMake):
```bash
cmake -S deps/Seto -B deps/Seto/build -DCMAKE_BUILD_TYPE=Release
cmake --build deps/Seto/build -j
```
Per aggiornare `Seto` all'ultima versione remota:
```bash
git submodule update --remote deps/Seto
```

## Utilizzo
```bash
python lean_to_sm.py examples/sample_proof.lean --out output/sample_proof.html
```
Per selezionare un teorema specifico da un file Lean grande (es. da `anthropics/formal-math`, `vp-vnp`):
```bash
python lean_to_sm.py path/to/Cuts.lean --theorem thm_onecut --out output/thm_onecut.html
```
Opzioni utili:
- `--theorem <name>`: seleziona un teorema/lemma specifico nel file `.lean`.
- `--seto-bin <path>`: percorso esplicito all'eseguibile `Seto` / `Seto.exe`.
- `--out <file.html>`: percorso del file HTML generato (default: `output/proof_sm.html`).
