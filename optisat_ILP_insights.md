# Insights: OptiSat v1.2.0 — ILP Certificate Verification Pipeline

**Fecha**: 2026-02-25
**Dominio**: lean4
**Estado del objeto**: upgrade (v1.1.0 → v1.2.0)
**Proyecto**: OptiSat (`~/Documents/claudio/lambdasat-lean/`)

---

## 1. Analysis del Objeto de Estudio

### Estado Actual (v1.1.0)

OptiSat v1.1.0 es un motor de equality saturation verificado con **233 teoremas, 0 sorry, 0 axiomas custom**. El teorema principal `full_pipeline_soundness` tiene cero hipótesis externas sobre reglas de reescritura.

**Gap principal**: El pipeline ILP (encoding → solving → certificate checking → extraction) tiene **30 definiciones y solo 3 teoremas** (10% cobertura). Las funciones de certificado (`checkSolution`, `checkRootActive`, `checkExactlyOne`, `checkChildDeps`, `checkAcyclicity`) no tienen pruebas de soundness.

### Objetivo v1.2.0

Verificar formalmente el pipeline de certificado ILP:
- **P0**: `checkSolution = true → ValidSolution` bridge theorem
- **P0**: Simp lemmas para accessors ILP (`isActive`, `getSelectedNodeIdx`, `getLevel`)
- **P1**: Correctness de `evalVar`, `checkConstraint`, `checkBounds`, `isFeasible`
- **P1**: `encodeEGraph` partial correctness (generación de constraints)

### Métricas Target

| Métrica | v1.1.0 | v1.2.0 Target |
|---------|--------|---------------|
| Theorems | 233 | ~248-253 |
| LOC | 8,627 | ~9,000-9,100 |
| Sorry | 0 | 0 |
| ILP theorem coverage | 10% (3/30) | ~60% (18/30) |

### Keywords

ILP certificate checking, ValidSolution, checkSolution soundness, constraint satisfaction,
Bool-to-Prop bridge, encoding correctness, e-graph extraction, TENSAT formulation,
acyclicity verification, level ordering, branch-and-bound, oracle-checker model,
certificate-based verification, proof-carrying optimization

---

## 2. Lecciones Aplicables

### 2.1 Lecciones Críticas (Tier 1 — Must Apply)

**L-250: ValidSolution unnecessary for extraction correctness**
> Si `extractILP` retorna `some expr`, todos los matches intermedios (`selectedNodes.get?`,
> `classes.get?`, bounds check, `mapOption`) ya tuvieron éxito. La hipótesis de éxito de
> extracción ya implica todo lo necesario. ValidSolution solo importa para **terminación**,
> no para correctness.
>
> **Implicación para v1.2.0**: El bridge `checkSolution → ValidSolution` es valioso para
> usuarios que quieran validar antes de extraer, pero NO es blocking para correctness.
> El teorema `extractILP_correct` ya asume `ValidSolution` — el bridge permite que
> `checkSolution` lo descargue computacionalmente.

**L-251: Double consistent_root_eq for ILP vs single for greedy**
> `extractILP` canonicaliza children via `root(root(c))`, requiriendo DOS aplicaciones de
> `consistent_root_eq` en el proof. `extractF` usa children directos, requiriendo solo una.
> Anticipar capas de composición de `root` en llamadas recursivas.

**L-209: beq_iff_eq es el bridge obligatorio Bool↔Prop**
> `beq_iff_eq.mp hc` : `(a == b) = true → a = b`
> `beq_iff_eq.mpr h` : `a = b → (a == b) = true`
> `cases hc : parent[j] == j` produce branches `true`/`false`, NO `=`/`≠`.

**L-173: Bool.false_eq_true + ite_false para reducir if-then-else con Bool**
> Después de probar `h : x = false`, `simp only [h]` NO reduce `if false = true then A else B`.
> Solución: `simp only [ha_false, Bool.false_eq_true, ite_false, ite_true]`

**L-107: `simp only [f]; split_ifs` — workflow estándar para funciones con predicados Bool**
> Aplicable directamente a `checkRootActive`, `checkExactlyOne`, `checkChildDeps`, `checkAcyclicity`.

**L-142: Equation lemmas para unfold selectivo**
> `rw [f.eq_5]` en lugar de `simp only [f]` para unfold solo un branch.
> Encontrar el índice correcto via `#check @f.eq_1`, `#check @f.eq_2`, etc.

**L-249: unfold + simp only [] + split para funciones con let bindings**
> `unfold fn at h; simp only [] at h; split at h`
> `simp only []` hace zeta-reduction (elimina let bindings) sin rewrite, exponiendo match para split.

**L-258: mapOption con 4 lemmas spec supera List.mapM para verificación**
> Custom `mapOption` con lemmas: nil, cons_inv, length, get.
> `mapOption_get`: `mapOption f l = some results → f l[i] = some results[i]`.
> Ya usado en `extractF_correct` y `extractILP_correct`.

**L-364: Option.bind_eq_some requiere simp only explícito desde Lean 4.9**
> NO es @[simp] por defecto. Usar `simp only [Option.bind_eq_some]`.

**L-181: Option.some.injEq at h — injection robusta en hipótesis**
> `simp only [Option.some.injEq] at h` convierte `some a = some b` a `a = b`.

### 2.2 Lecciones Estructurales (Tier 2)

**L-218: @Array.foldl_induction con tipos explícitos**
> `apply Array.foldl_induction` falla por unificación de orden superior con `.toList` en motive.
> Usar `exact @Array.foldl_induction` con TODOS los argumentos de tipo explícitos.

**L-398: Compound invariant para foldl_induction**
> Invariant compuesto debe incluir target property + WellFormed + UF size preservation.

**L-227: split (no by_cases) para if generado por foldl_induction**
> `by_cases` con `if_pos`/`if_neg` no hace match con formas sintácticas Fin-indexed vs Nat-indexed.
> `split` directamente.

**L-396: HashMap API pattern para Lean 4 Std**
> `simp [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]` luego `split`.

**L-240: split at hcls + simp para HashMap getElem?_insert**
> Después de simp crear if-then-else en hipótesis, `split at hcls` case-splits limpiamente.

**L-370: Extracción estratégica de lemmas controla elaboración**
> Lean 4 puede cambiar `HashMap.get?` a `getElem?` después de simp, rompiendo rw.
> Wrap problematic expressions en named definitions proved equal via rfl.

**L-375: Pattern.rec para inductivos anidados: motivos duales obligatorios**
> Cuando Pattern tiene `List (Pattern Op)`, standard induction falla.
> Usar `@Pattern.rec Op` con `motive_1` para Pattern y `motive_2` para List.

**L-379/L-384: Disjunctive foldl invariant Q(x) = x ∈ acc ∨ P(x)**
> Para probar `∀ x ∈ foldl f init l, P x`, el invariant debe ser disjuntivo.
> Al final, `Q(σ)` + `σ ∉ init` da `P(σ)` via `resolve_left`.

**L-311: Three-part soundness contract**
> (1) sufficient fuel for normal termination, (2) result evaluates correctly, (3) frame property.

**L-404: Small bridge lemmas son el pegamento para soundness a gran escala**
> Lemmas que parecen triviales (e.g., `Substitution.empty.get? = none`) son críticos.

### 2.3 Anti-patrones a Evitar

- **HashMap.fold para proofs** (L-200, L-302): No existe `fold_induction` en Std. Rediseñar para evitarlo. Usar `processKeys` pattern o probar propiedades desde extracción exitosa.
- **Full simp en proofs críticos** (L-319): Siempre `simp only [explicit_list]`.
- **Inline match en funciones WF-recursivas** (L-106, L-099): Causa kernel errors. Extraer a predicado booleano separado.
- **Asumir ValidSolution como prerequisito** (L-250, L-302): Explotar extracción exitosa en su lugar.
- **Monotonicity sin verificar TODOS los constructores** (L-143): Siempre verificar cada branch.
- **Type-indexed Expr con phantom types**: Causa proof explosion (10+ goals per match).

---

## 3. Bibliografía Existente Relevante

### 3.1 Documentos Clave

| Documento | Carpeta | Relevancia |
|-----------|---------|------------|
| **TENSAT** (Yang et al., 2021) | tensor-optimization | Define la formulación ILP canónica para e-graph extraction: variables binarias, one-hot por e-class, constraints de dependencia, ordering para acyclicity |
| **Fast and Optimal Extraction for Sparse E-Graphs** (Goharshady et al., 2024) | egraphs-treewidth | Algoritmo parameterizado para extracción óptima via treewidth DP |
| **Small Proofs from Congruence Closure** (Flatt et al., 2022) | criptografia/zk-circuitos | Certificados proof pequeños para e-graph congruence closure |
| **Semantic Foundations of Equality Saturation** (Suciu, 2025) | tensor-optimization | Semántica fixpoint formal vía tree automata; funda soundness de saturación |
| **egg: Fast and Extensible Equality Saturation** (Willsey et al., 2021) | egraphs-treewidth | Referencia canónica para greedy extraction y e-class analyses |
| **CompCert** (Leroy, 2006-ongoing) | verificacion | Patrón de simulación para verified optimization |
| **Verified Proof-Producing Union-Find** (Stevens, 2025) | criptografia/zk-circuitos | Union-find verificado en Isabelle con certificados |
| **ROVER: RTL Optimization via Verified E-Graph Rewriting** (Coward et al., 2024) | criptografia/zk-circuitos | Patrón de verificación para rewrite soundness |

### 3.2 Gaps Bibliográficos Identificados

1. **ILP solver verification literature**: No hay papers sobre branch-and-bound o simplex verificados formalmente en la biblioteca. Papers como VeriPB o CakeMLP lo cubrirían.
2. **Certificate formats for optimization solvers**: VIPR (Cheung et al., 2017) define un formato de certificado para MIP con inference rules verificables individualmente.
3. **Proof-carrying optimization**: El trabajo de Necula (1998) establece el framework teórico exacto para el modelo oracle-and-checker de OptiSat.
4. **E-graph extraction correctness proofs**: A pesar de cobertura extensiva de algoritmos, no hay paper formalizando la correctness proof de ILP-based extraction.

---

## 4. Estrategias y Decisiones Previas

### 4.1 Estrategias Ganadoras (Verificadas en Producción)

**Oracle-and-Checker Model** (VR1CS, OptiSat, SuperTensor):
> El ILP solver vive FUERA del TCB. Su output es validado por `checkSolution` (decidible).
> Correctness depende solo del verificador. Matches patrón de translation validation de CompCert.

**Three-Tier Invariant System** (VR1CS, OptiSat):
> EGraphWF → PostMergeInvariant → AddExprInv. Factorización clave para soundness incremental
> sin preservación de invariant monolítico.

**unfold + simp only [] + split** (L-301):
> Patrón universal para probar correctness de funciones recursivas con let bindings.
> Directamente aplicable a `checkRootActive`, `checkExactlyOne`, `checkChildDeps`, `checkAcyclicity`.

**mapOption con spec lemmas** (L-310):
> 4 lemmas (~40 LOC) amortizados en `extractF_correct` y `extractILP_correct`.

**Fuel-Based Termination** (5+ proyectos):
> Evita well-founded recursion opacity. Fuel compone via **max, no sum** (L-338).

### 4.2 Decisiones Arquitecturales Aplicables

**Certificate checking es SOUNDNESS, no COMPLETENESS** (VR1CS, OptiSat):
> Solo probar: `checkSolution = true → ValidSolution`. NO probar el reverso.
> Completeness es optimización, no correctness.

**De-risk con sketch ANTES de sublemmas** (L-134-L-137):
> Escribir statement con sorry intermedio. Verificar que type-checks antes de invertir en sub-lemmas.

**Theorem count overestimation factor: ~40-50%** (benchmarks históricos):
> Planificar para 50% fewer theorems que lo estimado. `unfold+simp+split` y typeclass laws
> eliminan muchos lemmas auxiliares anticipados.

### 4.3 Errores Evitados

- `ValidSolution` como prerequisito para extraction correctness → abandonado (L-302)
- `HashMap.fold` para proofs → pivotear a `processKeys` pattern (L-200)
- Custom typeclass `ValueAlgebra` → duplica Mathlib, pierde `simp;ring` (amo-lean)

### 4.4 Benchmarks de Referencia

| Módulo | LOC | Theorems | Densidad |
|--------|-----|----------|----------|
| ILPCheck.lean (actual) | 133 | 1 | 7.5/KLOC |
| ILPSpec.lean (actual) | 136 | 3 | 22.1/KLOC |
| ExtractSpec.lean (ref) | 132 | 3 | 22.7/KLOC |
| Target v1.2.0: ILP pipeline | ~470 new | ~15-20 | ~32-43/KLOC |

---

## 5. Nueva Bibliografía Encontrada (Online)

### 5.1 Tier 1: Directamente Aplicable

**VIPR: Verifying Integer Programming Results** (Cheung, Gleixner, Steffy, 2017)
> Define formato de certificado para MIP: lista de statements verificados secuencialmente
> con inference rules limitadas. Cada regla es simple → verificable por `decide`/`omega`.
> El bridge "checker says OK → result is valid" se logra por inducción estructural sobre
> el formato del certificado.
> *Aplicación directa*: Descomponer `checkSolution` en checks individuales, cada uno probado
> por `decide`, luego componer.

**SMT-Based MILP Certificate Verification** (arXiv:2312.10420, 2023-2025)
> Codifica inference rules de VIPR como ground formulas que caracterizan completamente
> la validez del check algorítmico. La correctness del encoding fue verificada usando Why3.
> *Aplicación directa*: Expresar `checkSolution = true ↔ ValidSolution` como ground formula.

**Verified Solver for Linear Mixed Integer Arithmetic** (Isabelle/HOL, 2020)
> Branch-and-bound formalmente verificado en Isabelle/HOL. Pruebas mecanizadas de que
> todo set satisfactible de desigualdades lineales enteras tiene una solución pequeña
> con upper bounds explícitos. Bridge completo de algorithmic check a formal soundness.

**Certifying MIP-Based Presolve Reductions for 0-1 ILPs** (CPAIOR 2024)
> Correctness de MIP presolve reductions en **0-1 ILPs** (variables binarias, exactamente
> como e-graph extraction ILP) certificada usando VeriPB pseudo-Boolean proof logging.
> *Directamente relevante*: e-graph extraction ILP es un 0-1 ILP.

### 5.2 Tier 2: Patrón Arquitectural

**AMO-Lean: Verified Optimization via Equality Saturation in Lean 4** (LambdaClass, 2025)
> Implementa equality saturation en Lean 4 con rewrite rules verificadas formalmente.
> Soundness chain: `applyFirst_sound → rewriteBottomUp_sound → rewriteToFixpoint_sound → simplify_sound`.
> Usa greedy extraction (NO ILP). El patrón de layered soundness es directamente aplicable.

**Guided Equality Saturation** (POPL 2024, Koehler et al.)
> Equality saturation como Lean 4 tactic. Soundness by kernel checking (translation validation).
> Insight arquitectural clave: ni el engine ni egg están en el TCB — un bug solo resulta
> en tactic failure. Sidesteps the need to verify the ILP solver.

**Improving Term Extraction with Acyclic Constraints** (EGRAPHS 2023, He)
> Directamente aborda el **cycle problem** en ILP extraction. Propone encoding explícito
> de acyclic constraints como disjunctions of conjunctions of negated e-node variables.
> Crítico para `encodeEGraph` correctness — standard ILP encodings offload topological
> sorting al solver, lo cual no escala.

**Semantic Foundations of Equality Saturation** (ICDT 2025, Suciu)
> Fundaciones matemáticas rigurosas: semántica fixpoint vía tree automata.
> Extraction correctness sigue de la propiedad de fixpoint.

---

## 6. Insights de Proyectos Hermanos

### 6.1 VR1CS-Lean

- `extractILP_correct` proof skeleton: inducción sobre fuel → split on options → membership conversion → invariant extraction → cases on operation. **100% reutilizable** con domain-generalization.
- **Gap idéntico**: NO tiene `checkSolution → ValidSolution` bridge. El bridge debe construirse from scratch.
- 8 `@[simp]` lemmas para `NodeEval` variants — patrón para ILP accessor simp lemmas.
- `mapOption` spec lemmas (4 lemmas, ~40 LOC) ya portados a OptiSat.

### 6.2 SuperTensor-lean

- `checkFeasibility` (ILPExtract.lean:145-163): Pattern de constraint matching distinguiendo partial vs complete assignment. **Modelo directo** para `checkSolution` decomposition.
- `buildILP` (ILPExtract.lean:71-129): Three-phase encoding (reachability + variable gen + constraints). Template para `encodeEGraph` correctness.
- `isValidTreeDecomp_true_implies_properties`: **Bool→Prop bridge via `&&` decomposition**. El patrón exacto: probar cada componente `&&` individualmente, luego componer.
- Layered WF predicates (CoreSpec:16-55): 5-tier validation desde primitives hasta estructura completa. Modelo para `ILPProblemWF`.

### 6.3 ProofKit

- `Foldl.foldl_inv_extends` y `foldl_pair_inv_pred`: Directamente aplicables para probar que iteraciones de ILP checking preservan invariants.
- `HashMap.get_insert_eq` / `get_insert_ne`: Para razonar sobre HashMap lookups en certificate construction.
- **NO tiene** infraestructura de certificate checking ni Bool→Prop bridges.
- Integración vía local path dependency en `lakefile.toml`: `[[require]] name = "proofkit" path = "../proofkit"` (misma toolchain v4.26.0).

### 6.4 DynamicTreeProg

- `treeFold_lower_bound` (NiceTree:113-124): Si cada paso de DP preserva "result ≤ cost", el traversal completo también. **Aplicable** a probar que ILP extraction yield es lower bound on optimal cost.
- `depth_lt_size` (TreePath:130-143): depth < size. **Directamente aplicable** a e-graph traversal termination (fuel sufficiency para `extractILPAuto`).
- `treeFold_inv` (StateTransform): Invariant propagation through tree-structured computation. Patrón para constraint propagation verification.
- **NO tiene** Bool→Prop bridges, ILP proofs, ni constraint satisfaction.

---

## 7. Síntesis de Insights

### 7.1 Hallazgos Clave (Top 10)

1. **ValidSolution es puente, no prerequisito** (L-250): El bridge `checkSolution → ValidSolution` es para la API del usuario, no para correctness interna. `extractILP_correct` ya funciona con la hipótesis `ValidSolution`; el bridge permite que los usuarios la descarguen computacionalmente.

2. **Decomposición Bool→Prop vía `&&`** (SuperTensor pattern): `checkSolution = check1 && check2 && check3 && check4`. Probar cada `checkN = true → PropN` por separado, luego componer con `Bool.and_eq_true_iff`. Es el patrón más limpio, ya probado en SuperTensor.

3. **HashMap.fold es intractable** (L-200, L-302): Ninguno de los 4 proyectos hermanos tiene proofs sobre `HashMap.fold`. Evitar a toda costa. Probar propiedades desde la estructura del resultado, no del proceso de construcción.

4. **encodeEGraph es el item más difícil** (~120 LOC): Involucra un fold sobre classes con state threading complejo. La estrategia de SuperTensor (three-phase: reachability → variables → constraints) es la descomposición correcta, pero la proof involucra compound invariants (L-398).

5. **Theorem count overestimation ~40-50%**: Basado en benchmarks históricos de 5 proyectos. `unfold+simp+split` elimina muchos lemmas auxiliares. Planificar 15-20 nuevos teoremas, no 25-30.

6. **VIPR certificate format es el modelo correcto**: Certificado = secuencia de checks simples, cada uno verificable por `decide`/`omega`. Inducción estructural sobre el formato da el bridge completo.

7. **Acyclicity check requiere pigeonhole** (L-203): `checkAcyclicity` usa level ordering. La prueba de soundness requiere mostrar que levels implican no-cycles. Esto necesita pigeonhole argument (unique en usar `Classical.em` en el proyecto).

8. **Fuel sufficiency para extractILPAuto** vinculable a `depth_lt_size` (DynamicTreeProg): numClasses+1 como fuel es sufficient para soluciones acíclicas porque depth < size en DAGs.

9. **ProofKit foldl_inv es reutilizable directamente** para los loops iterativos de checking, pero NO es un dependency blocker — se puede copiar el teorema individualmente si no queremos la dependencia.

10. **AMO-Lean confirma el patrón de layered soundness** en Lean 4 production. Su chain `rule_sound → loop_sound → extraction_sound` es isomórfica a OptiSat. Validación independiente del approach.

### 7.2 Riesgos Identificados

| Riesgo | Probabilidad | Impacto | Mitigación |
|--------|:---:|:---:|---|
| `encodeEGraph` proof complexity exceeds estimate | Alta | Alto | De-risk con sketch (`_aux` pattern). Probar statement type-checks antes de sub-lemmas |
| HashMap.fold needed for encode proof | Media | Alto | Rediseñar: probar propiedades de constraints desde su estructura, no del fold que los generó |
| Lean 4 elaboration fights (get?/getElem?) | Alta | Bajo | L-370: wrap en named defs, puentes explícitos |
| checkAcyclicity requiere Classical.em | Baja | Bajo | Ya usado una vez en UnionFind.lean. Aceptable |
| Scope creep hacia completeness | Media | Medio | Firme: solo soundness. "checkSolution → ValidSolution", no el reverso |

### 7.3 Orden de Implementación Recomendado

```
═══════════════════════════════════════════════════════════════
 BLOQUE A: ILP Simp Lemmas + Accessor Proofs (LOW risk, ~30 LOC)
═══════════════════════════════════════════════════════════════

  A.1  @[simp] isActive_def : sol.isActive classId = ...
  A.2  @[simp] getSelectedNodeIdx_def : sol.getSelectedNodeIdx classId = ...
  A.3  @[simp] getLevel_def : sol.getLevel classId = ...
  A.4  @[simp] numVars_def, numConstraints_def

  Estrategia: unfold + rfl. ~5 lemmas, ~15 LOC.
  Lecciones: L-286 (specialized simp lemmas outperform general ones)

═══════════════════════════════════════════════════════════════
 BLOQUE B: checkSolution Decomposition (MEDIUM risk, ~150 LOC)
═══════════════════════════════════════════════════════════════

  B.1  checkRootActive_sound:
       checkRootActive sol rootId = true → sol.isActive rootId = true
       Estrategia: unfold + simp [isActive_def] + split (L-107)
       Lecciones: L-209 (beq_iff_eq), L-173 (Bool.false_eq_true + ite_false)
       ~20 LOC

  B.2  checkExactlyOne_sound:
       checkExactlyOne g sol = true → ∀ classId, sol.isActive classId →
         ∃ idx, sol.getSelectedNodeIdx classId = some idx ∧
                idx < (g.classes.get? classId).get!.nodes.size
       Estrategia: Array.all → forall bridge, luego unfold + split.
       Lecciones: L-218 (foldl_induction explicit), L-379 (disjunctive invariant)
       ~40 LOC

  B.3  checkChildDeps_sound:
       checkChildDeps g sol = true → ∀ classId nodeIdx,
         sol.isActive classId → sol.getSelectedNodeIdx classId = some nodeIdx →
         ∀ child ∈ children(node), sol.isActive (root g.unionFind child)
       Estrategia: Similar a B.2. Double iteration (classes × children).
       Lecciones: L-251 (double root), L-396 (HashMap API)
       ~40 LOC

  B.4  checkAcyclicity_sound:
       checkAcyclicity g sol = true → ∀ classId nodeIdx,
         sol.isActive classId → sol.getSelectedNodeIdx classId = some nodeIdx →
         ∀ child ∈ children(node),
           sol.getLevel (root g.unionFind child) < sol.getLevel classId
       Estrategia: Level ordering → no-cycles. Possible need for pigeonhole.
       Lecciones: L-203 (pigeonhole for acyclicity), L-125 (freshness by boundedness)
       ~50 LOC

  B.5  checkSolution_sound (composition):
       checkSolution g rootId sol = true → ValidSolution g rootId sol
       Estrategia: Decompose && via Bool.and_eq_true_iff, apply B.1-B.4.
       Modelo: SuperTensor isValidTreeDecomp pattern.
       ~15 LOC

═══════════════════════════════════════════════════════════════
 BLOQUE C: Certificate Evaluation (MEDIUM risk, ~85 LOC)
═══════════════════════════════════════════════════════════════

  C.1  evalVar_correct:
       evalVar sol varId = some val → sol.assignment.get? varId = some val
       Estrategia: unfold + simp [HashMap.get?_eq_getElem?]
       ~15 LOC

  C.2  evalConstraintLHS_correct:
       Relates linear combination evaluation to mathematical definition
       Estrategia: Induction on coefficient list, foldl_induction pattern.
       Lecciones: L-218, L-398 (compound invariant)
       ~25 LOC

  C.3  checkConstraint_correct:
       checkConstraint c sol = true → constraintSatisfied c sol
       Estrategia: Cases on operator (le/ge/eq), then omega/decide.
       Lecciones: L-107 (simp + split_ifs), L-142 (equation lemmas)
       ~20 LOC

  C.4  checkBounds_correct + isFeasible_sound:
       isFeasible sol problem = true → ∀ c ∈ problem.constraints,
         constraintSatisfied c sol
       Estrategia: Array.all → forall bridge, compose C.1-C.3.
       ~25 LOC

═══════════════════════════════════════════════════════════════
 BLOQUE D: encodeEGraph Partial Correctness (HIGH risk, ~120 LOC)
═══════════════════════════════════════════════════════════════

  D.1  encodeEGraph_root_constraint:
       Root class activation constraint is generated
       ~25 LOC

  D.2  encodeEGraph_exactlyOne_per_class:
       For each reachable class, an exactlyOne constraint is generated
       Estrategia: Induction on reachable classes, track generated constraints.
       Lecciones: L-398 (compound invariant), L-218 (foldl_induction)
       ~40 LOC

  D.3  encodeEGraph_child_deps:
       For each node in each class, dependency constraints link to child classes
       ~40 LOC

  D.4  encodeEGraph_acyclicity:
       Level ordering constraints are generated for cycle prevention
       ~25 LOC (may be simpler than B.4, just proving generation)

  NOTA: D.1-D.4 prueban que los constraints se GENERAN correctamente,
  no que IMPLICAN ValidSolution. El bridge es Bloque B.

═══════════════════════════════════════════════════════════════
 BLOQUE E: extractILPAuto Fuel Sufficiency (LOW risk, ~30 LOC)
═══════════════════════════════════════════════════════════════

  E.1  extractILPAuto_fuel_sufficient:
       checkSolution g rootId sol = true →
       extractILPAuto g sol rootId = extractILP g sol rootId (numClasses g + 1)
       Estrategia: Relate acyclicity levels to depth bound (DynamicTreeProg
       depth_lt_size pattern). numClasses+1 fuel ≥ max depth.
       ~20 LOC

  E.2  solutionCost_correct:
       solutionCost g sol = Σ cost(selectedNode) for active classes
       ~10 LOC

```

### 7.4 Resumen de Esfuerzo

| Bloque | Tipo | LOC Est. | Theorems Est. | Riesgo |
|--------|------|:---:|:---:|:---:|
| A: Simp lemmas | HOJA | ~30 | 5 | LOW |
| B: checkSolution bridge | CRÍTICO | ~150 | 5 | MEDIUM |
| C: Certificate evaluation | PARALELO | ~85 | 4 | MEDIUM |
| D: encodeEGraph partial | FUNDACIONAL | ~120 | 4 | HIGH |
| E: Fuel sufficiency | HOJA | ~30 | 2 | LOW |
| **TOTAL** | | **~415** | **~20** | |

**Nota**: Aplicando el factor de overestimation (L-benchmarks), el total real será ~250-330 LOC y ~12-15 theorems.

### 7.5 Dependencias entre Bloques

```
A (simp lemmas) ─────────────────┐
                                 ↓
B (checkSolution bridge) ←── uses A.1-A.3
  B.1 (root active)        │
  B.2 (exactly one) ───────┤
  B.3 (child deps) ────────┤
  B.4 (acyclicity) ────────┤
  B.5 (composition) ←── B.1+B.2+B.3+B.4
                                 │
C (cert evaluation) ←───── independent of B
  C.1 (evalVar) ───────────┤
  C.2 (constraintLHS) ─────┤
  C.3 (checkConstraint) ───┤
  C.4 (isFeasible) ←── C.1+C.2+C.3
                                 │
D (encodeEGraph) ←──── independent of B,C
  D.1-D.4 ─────────────────┤
                                 │
E (fuel sufficiency) ←── B.4 (acyclicity) + D
```

**Ejecución paralela posible**: B y C son independientes. D es independiente de B,C.
**Secuencial obligatorio**: A → B.5, B.4 → E.

### 7.6 Recomendaciones para Planificación

1. **Empezar por A + B.1** (most constrained, lowest risk): Establece simp lemmas y primer bridge. Validates the approach before investing in harder items.

2. **De-risk D con sketch**: Antes de B.2-B.4, escribir `encodeEGraph_root_constraint_aux` con sorry para verificar que la decomposición es viable.

3. **C es independiente y parallelizable**: Puede ejecutarse en paralelo con B si hay Agent Teams disponibles.

4. **E es el cierre natural**: Depende de B.4 (acyclicity) y D (encoding). Ejecutar último.

5. **Considerar ProofKit dependency**: Si `foldl_inv_extends` se usa en ≥3 pruebas, vale la pena agregar como dependency Lake. Si solo 1-2 usos, copiar el lemma directamente.

6. **NO intentar completeness** de checkSolution (¬ValidSolution → checkSolution = false). Es sound-only.

7. **Tag v1.2.0** al completar Bloques A+B. Tag v1.2.1 si se completan C+D+E.

### 7.7 Recursos Prioritarios

1. **L-250** (ValidSolution unnecessary) — reframe de todo el esfuerzo P0
2. **L-107 + L-249** (unfold+split workflow) — patrón proof para los 4 check lemmas
3. **SuperTensor ILPExtract.lean:145-163** — modelo de `checkFeasibility` decomposition
4. **VR1CS ILPSpec.lean:33-140** — `extractILP_correct` proof skeleton
5. **VIPR paper** (arXiv:1611.08832) — certificate format design for composition
6. **ProofKit Foldl module** — `foldl_inv_extends` para iteration proofs
7. **DynamicTreeProg NiceTree:113-124** — `treeFold_lower_bound` para fuel sufficiency
