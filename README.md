# seto-lean

Decomposizione di dimostrazioni **Lean 4** in **State Machines** tramite **Seto 2.0** con visualizzazione interattiva HTML/SVG.

## Dipendenze
`deps/Seto` è collegato come **git submodule** verso `https://github.com/viktorteren/Seto.git`:
```bash
git submodule update --init --recursive
```
Per aggiornare `Seto` all'ultima versione remota:
```bash
git submodule update --remote deps/Seto
```

## Utilizzo rapido
```bash
python lean_to_sm.py examples/sample_proof.lean --out output/sample_proof.html
```
Poi apri `output/sample_proof.html` nel browser:
- ogni **State Machine** estratta da `Seto` viene mostrata come diagramma leggibile;
- le tattiche **blu** sono locali/parallele, quelle **ambra** sono punti di sincronizzazione tra più SM;
- cliccando una tattica si evidenzia la riga esatta nel codice `.lean`.
