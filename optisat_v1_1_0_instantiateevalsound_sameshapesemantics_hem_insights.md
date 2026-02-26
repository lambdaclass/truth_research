# Insights: OptiSat v1.1.0 — Probar InstantiateEvalSound, SameShapeSemantics, hematch_bnd

**Fecha**: 2026-02-24
**Dominio**: lean4
**Estado del objeto**: upgrade (v1.0.0 → v1.1.0)

---

## 1. Análisis del Objeto de Estudio

### Resumen

OptiSat v1.1.0 busca **cerrar las 3 últimas hipótesis no descargadas** del Path B de soundness (`full_pipeline_soundness_internal`), transformándolas de asunciones del usuario en teoremas internos del motor. Además, cubre las recomendaciones P1-P5 de la autopsia (README stale, SlimCheck, ILP coverage, edge-case tests, TCB boundary docs).

Las 3 hipótesis son:

| Hipótesis | Definida en | Tipo | Complejidad |
|-----------|-------------|------|-------------|
| **InstantiateEvalSound** | EMatchSpec:500-517 | `instantiateF` preserva (CV, PMI, SHI) + valor correcto | **ALTA** |
| **SameShapeSemantics** | EMatchSpec:58-69 | ops con `sameShape = true` evalúan igual si hijos coinciden | **MEDIA** |
| **hematch_bnd** | TranslationValidation:195-199 | `ematchF` produce sustituciones acotadas | **MEDIA-BAJA** |

### Keywords

instantiateF, SameShapeSemantics, ematchF, ConsistentValuation, PostMergeInvariant, SemanticHashconsInv, Pattern.eval, substVal, AllDistinctChildren, fuel-based recursion, foldl induction, forward preservation, existential threading, typeclass parameterization, SlimCheck

### Gaps identificados

| ID | Gap | Ubicación | Complejidad |
|----|-----|-----------|-------------|
| G1 | `InstantiateEvalSound` — preserva triple + valor correcto | EMatchSpec:500 | ALTA |
| G2 | `SameShapeSemantics` — derivable de evalOp_ext + sameShape | EMatchSpec:58 | MEDIA |
| G3 | `hematch_bnd` — ematchF sustituciones acotadas | TV:195 | BAJA |
| G4 | README metrics stale (218→226 thm, 7748→6899 LOC) | README.md | TRIVIAL |
| G5 | Zero SlimCheck properties en codebase | — | MEDIA |
| G6 | ILPCheck functions sin theorem coverage | ILPCheck.lean | BAJA |
| G7 | No #eval edge-case tests (empty graph, fuel=0, etc.) | Tests/ | BAJA |
| G8 | TCB boundary undocumented para ParallelMatch/ParallelSaturate | README/ARCH | BAJA |

### Dependencias (orden topológico)

```
G2 SameShapeSemantics ──┐
                        ├──→ G1 InstantiateEvalSound ──→ G4+G8 Docs
G3 hematch_bnd ─────────┘                                  ↑
                                                   G5+G6+G7 Tests
```

---

## 2. Lecciones Aplicables

### Lecciones reutilizables (Top 15)

| ID | Título | Aplicación en v1.1.0 |
|----|--------|---------------------|
| **L-391** | InstantiateEvalSound as focused assumption replacing monolithic PreservesCV | Core strategy: descomponer PreservesCV → 3 props verificables independientes |
| **L-377** | SameShapeSemantics as standalone Prop (no typeclass field) | No romper NodeSemantics; asumir solo donde se necesita |
| **L-386** | SameShapeSemantics as abstract bridge for ematchF_sound | En node case: usar SSS para probar evalOp skelOp env w = evalOp nd.op env v |
| **L-378** | Strengthened IH with SubstExtends for sequential foldl | IH de ematchF/instantiateF debe valer para ALL extensions de σ |
| **L-383** | SubstExtends: child i correctness bajo substitución final | La IH para child i debe valer bajo σ_final, no solo σ_intermedia |
| **L-390** | foldl soundness via List induction + suffices generalization | Patrón para hematch_bnd y applyRulesF |
| **L-375** | Pattern.rec with dual motives for nested inductives | Evitar mutual recursion: motive₁ para Pattern, motive₂ para List Pattern |
| **L-382** | Pattern.rec dual motives: map equality en list motive | Element motive maneja eval individual; list motive maneja map eval equality |
| **L-234** | AddExprInv — invariante débil para inducción recursiva | Cuando EGraphWF no se preserva, factorizar sub-invariante preservable |
| **L-392** | Value agreement monotonicity through size bounds | Rastrear size monotonicity + value agreement; componen por transitividad |
| **L-218** | `exact @Array.foldl_induction` con tipos explícitos | Lean 4 no unifica .toList en patterns; usar `exact` con @ |
| **L-227** | `split` no `by_cases` para `if` en goals | `split` matchea cualquier forma sintáctica de condicional |
| **L-388** | suffices to factor sideCondCheck before instantiateF match | Cuando hay match anidado, usar suffices para probar rama principal primero |
| **L-369** | Explicit Invariants for State-Passing Recursion | Threading state requiere invariantes explícitas preservation por step |
| **L-312** | Zero Sorry Audit as final gate | Gate final: 0 sorry, 0 axiom, 0 admit, 0 native_decide |

### Anti-patrones a evitar

1. **L-138: Fundacional como debt** — InstantiateEvalSound es FUNDACIONAL (otros dependen de él). NUNCA diferirlo.
2. **L-269: LLM QA false positives** — Kernel verification > LLM analysis. Confiar en `lake build` + `lean_verify`.
3. **L-351: Example-based verification es insuficiente** — 8 tests con decide NO constituyen prueba formal.
4. **IH no generalizada (L-243)** — Si IH de instantiateF depende de valuación v, generalizar: `∀ v', agrees v' v → P v'`.
5. **Invariante monolítico en loop (L-222)** — NO probar hematch_bnd con EGraphWF global. Factorizar con PostMergeInvariant.

### Técnicas críticas

1. **Descomposición de obligaciones monolíticas** (L-391, L-394): PreservesCV → ematchF_sound + PatternSoundRule + InstantiateEvalSound
2. **Bridges con standalone Props** (L-377, L-381, L-386): SameShapeSemantics como Prop, no typeclass field
3. **Strengthened IH para foldl secuencial** (L-378, L-383): `SubstExtends subst0 sigma AND ∀ sigma', SubstExtends sigma sigma' → P sigma'`
4. **Dual motives para nested inductives** (L-375, L-382): `@Pattern.rec (motive₁ : Pattern Op → Prop) (motive₂ : List (Pattern Op) → Prop)`
5. **Forward preservation chain** (L-392): `v_new agrees v_old on g.uf.size → componer por transitividad`

---

## 3. Bibliografía Existente Relevante

### Documentos clave (lectura prioritaria para v1.1.0)

| # | Documento | Año | Relevancia | Insight clave |
|---|-----------|-----|-----------|---------------|
| 1 | **Selsam & de Moura — Congruence Closure in ITT** | 2016 | CRÍTICO | hcongrn lemmas, UF.WF preservation durante rebuild, separación structural/semantic |
| 2 | **Suciu et al. — Semantic Foundations of Equality Saturation** | 2025 | CRÍTICO | Tree automata, fixpoint semantics, acyclicity criterion, chase procedure |
| 3 | **de Moura & Bjørner — Efficient E-matching for SMT Solvers** | 2007 | CRÍTICO | E-matching code trees, inverted path index, substitution boundedness |
| 4 | **Rossel & Goens — Bridging Syntax and Semantics of Lean Expressions in E-Graphs** | 2024 | CRÍTICO | Lean expression normalization, sameShape conceptual basis, de Bruijn |
| 5 | **Rossel, Goens et al. — Pen-and-Paper Equational Reasoning in ITPs via EqSat** | 2026 | CRÍTICO | Conditional rewrite rules en Lean, proof reconstruction, typeclass erasure |
| 6 | **Zhang et al. — Relational E-matching** | 2022 | ALTO | Worst-case optimal matching, conjunctive query reduction, complexity bounds |

### Gaps bibliográficos

| Gap | Impacto | Mitigación |
|-----|---------|-----------|
| No existen papers sobre formalización de e-graph ops en Lean 4 | CRÍTICO | OptiSat ES ese paper. Usar Selsam (CC en ITT) + Rossel (Lean bridging) como templates |
| Typeclass-parameterized e-graphs no documentado | CRÍTICO | Adaptar ROVER (conditional rules) + técnicas propias de v0.1.0-v1.0.0 |
| Mechanized proof of ematch boundedness | MEDIO | Combinar de Moura (code trees) + Zhang (relational, complexity bounds) |

---

## 4. Estrategias y Decisiones Previas

### Estrategias ganadoras (verificadas en producción)

| Estrategia | Proyecto | Resultado | Aplicación v1.1.0 |
|-----------|----------|-----------|-------------------|
| **3-Tier Invariant** | VR1CS v1.3.0, OptiSat v0.3.0 | EGraphWF → PMI → AddExprInv | Factorizar InstantiateEvalSound con sub-invariantes |
| **CV como Prop Pivot** | OptiSat v0.2.0+ | 40+ thms threading CV | Las 3 hipótesis deben preservar/usar CV |
| **De-risk crítico ANTES** | OptiSat v1.0.0 (ematchF_sound) | F7S3 de-risked con sketch | Sketch InstantiateEvalSound antes de probar |
| **∃v' existencial** | OptiSat v0.2.0 (merge_consistent) | No preservar v exacto, sino ∃v' | InstantiateEvalSound produce ∃v' con agreement |
| **SemanticHashconsInv** | OptiSat v0.3.0 | Cerró sorry de rebuild | Reutilizable para InstantiateEvalSound (preservar SHI) |

### Patrones de prueba reutilizables

1. **Patrón Invariante Débil (L-234)**: `AddExprInv` preservable recursivamente cuando `EGraphWF` no lo es. Aplicar a InstantiateEvalSound.
2. **Patrón Forward Preservation (L-237/L-392)**: Threading `v' agrees v on g.uf.size` a través de foldl steps. Aplicar a hematch_bnd.
3. **Patrón Workhorse Split (L-235)**: `simp only [fn]; split; · hit case; · miss case`. Aplicar a InstantiateEvalSound cases.
4. **Patrón foldl con Membership (L-148)**: `foldl_invariant_mem` para preservar propiedad a través de lista. Aplicar a SameShapeSemantics.
5. **Patrón Array.foldl_induction (L-218/L-227)**: `exact @Array.foldl_induction` con tipos explícitos + `split` para ifs.

### Cómo se cerraron gaps similares

**v0.3.0 (rebuildStepBody sorry)**:
- Problema: `rebuildStepBody` requería EGraphWF pero solo PMI disponible
- Solución: Definir SemanticHashconsInv, probar que processClass preserva SHI bajo PMI
- Resultado: 3-5 nuevos teoremas, ~80 LOC, 0 sorry

**v1.0.0 (ematchF_sound)**:
- Problema: No había prueba de que ematchF encuentra matches válidos
- Solución: Definir Pattern.eval, probar ematchF_sound por inducción sobre Pattern
- Resultado: 5 nuevos teoremas, 0 sorry, PreservesCV eliminado del API

**Patrón extrapolable a v1.1.0**: Definir semántica auxiliar → probar preservation → componer en pipeline.

---

## 5. Nueva Bibliografía Encontrada

Sección omitida — la biblioteca existente (68 documentos) cubre ampliamente el tema. Los 6 papers clave listados en Sección 3 son suficientes.

---

## 6. Insights de Nueva Bibliografía

Sección omitida — sin descargas nuevas necesarias.

---

## 7. Síntesis de Insights

### Hallazgos clave (Top 10)

1. **InstantiateEvalSound es una generalización de `instantiateF_preserves_consistency` (SaturationSpec:233)**. Ya existe prueba parcial: preserva (CV, PMI). Falta agregar SHI + valor correcto (`v'(root id) = Pattern.eval pat env (substVal v g.uf σ)`). La estructura inductiva sobre Pattern ya fue resuelta en ematchF_sound (v1.0.0).

2. **SameShapeSemantics debería derivarse de `evalOp_ext` (NodeSemantics axiom)**. `evalOp_ext` dice que evalOp depende de v solo a través de children. Si `sameShape op₁ op₂ = true` implica mismos children indices (solo diferente identidad), y v₁/v₂ coinciden en esos children, entonces evalOp coincide. La prueba es una aplicación directa.

3. **hematch_bnd es una propiedad estructural de ematchF**. `ematchF` solo asigna IDs que ya existen en el grafo (obtiene IDs de `g.classes` y `g.hashcons`). Por inducción sobre Pattern + fuel, cada σ.get? retorna IDs < g.uf.size. Reutiliza `matchChildren_sound` (ya probado).

4. **El patrón de v0.3.0 (SemanticHashconsInv) es directamente reutilizable** para InstantiateEvalSound. La clave es que `instantiateF` hace `add` (que preserva SHI por `add_node_consistent` composición) y no hace `merge` directo (solo el caller lo hace después).

5. **`instantiateF` NO hace merge — solo `add`**. Esto simplifica enormemente InstantiateEvalSound: no necesita probar merge_preserves_shi (ya probado), solo add_preserves_shi (más fácil). La complejidad real está en el caso `node` con foldl sobre subpats.

6. **Dual motives son OBLIGATORIOS** (L-375, L-382) para inducción sobre Pattern (que contiene `List (Pattern Op)`). Sin ellos, Lean 4 no genera recursor correcto. Patrón ya usado exitosamente en Pattern.eval_ext (EMatchSpec:107-128).

7. **SameShapeSemantics NO necesita ser un teorema genérico** si se reformula como axiom de typeclass. Opción A: probar genéricamente de evalOp_ext. Opción B: agregar como campo de NodeSemantics. L-377 recomienda Prop standalone (Opción A) para no romper la typeclass.

8. **hematch_bnd tiene una dependencia oculta**: necesita que `ematchF` NO cree nuevos IDs (solo lee). Verificar que `ematchF` es read-only sobre el grafo (no muta). Si ematchF es puro (no add/merge), la prueba es trivial.

9. **Las recomendaciones P1-P5 son trabajo mecánico** que puede hacerse en paralelo con las pruebas formales. P1 (README update) y P4 (edge-case tests) son independientes. P2 (SlimCheck) requiere `import Mathlib.Testing.SlimCheck` — pero OptiSat es self-contained sin Mathlib. SlimCheck properties serían en un archivo Test separado.

10. **El README claim de "218 theorems" vs 226 actual sugiere que las últimas edits de v1.0.0 no actualizaron README**. El autopsy también encontró 6,899 LOC vs 7,748 claimed. Ambos números deben corregirse al cerrar v1.1.0.

### Riesgos identificados

| Riesgo | Severidad | Mitigación |
|--------|-----------|-----------|
| InstantiateEvalSound foldl sobre subpats con threading existencial de v' | ALTA | Reutilizar patrón de processClass_shi_combined (SemanticSpec:1168): exact @Array.foldl_induction con threading |
| SameShapeSemantics: sameShape puede no implicar same children length | MEDIA | Verificar definición de sameShape; ya existe `sameShape_children_length` (EMatchSpec:39) |
| hematch_bnd: ematchF puede crear nodos via side effects | MEDIA | Verificar que ematchF es read-only (lee g, no lo muta). Si muta, bounds cambian |
| SlimCheck requiere Mathlib (OptiSat es self-contained) | BAJA | Archivo test separado con `require mathlib` solo en tests, o skip P2 |
| Regression en compile time con +300 LOC de proofs | BAJA | Benchmark compile time antes/después; target <45s |

### Recomendaciones para planificación

#### Fase 8: Discharge Hypotheses (v1.1.0 core)

**DAG propuesto**:

```
F8S1 SameShapeSemantics_holds [FUND] ──────────────────┐
F8S2 ematchF_substitution_bounded [FUND] ──────────────┤
                                                       ├──→ F8S4 Update signatures [HOJA]
F8S3 InstantiateEvalSound_holds [CRIT/GATE, deps: S1] ┘
```

**Bloques**:
- Bloque 20: F8S1 + F8S2 (paralelo, ~120-180 LOC)
- Bloque 21: F8S3 (secuencial, GATE de-risk, ~150-200 LOC)
- Bloque 22: F8S4 + P1-P5 (mecánico, ~100 LOC)

#### Fase 8 Addendum: Autopsy P1-P5

| Rec | Acción | Bloque |
|-----|--------|--------|
| P1 | Actualizar README.md: theorem count, LOC count | 22 |
| P2 | SlimCheck — SKIP o archivo test separado (requiere Mathlib) | 22 o defer |
| P3 | ILPCheck individual function properties — considerar #eval tests | 22 |
| P4 | Edge-case #eval tests: empty graph, self-merge, fuel=0 | 22 |
| P5 | Documentar TCB boundary para Parallel* en README | 22 |

### Recursos prioritarios (Top 5)

1. **L-391 + L-394**: InstantiateEvalSound decomposition + PreservesCV elimination strategy
2. **L-378 + L-383**: Strengthened IH with SubstExtends (CRÍTICO para foldl proofs)
3. **L-375 + L-382**: Dual motives for Pattern.rec (OBLIGATORIO para induction)
4. **Selsam & de Moura 2016**: Congruence closure in ITT — foundation conceptual
5. **OptiSat EMatchSpec:340-467** (ematchF_sound_strong): template directo para hematch_bnd

---

## Appendix A: Análisis detallado de cada hipótesis

### A.1 SameShapeSemantics (estimado: 60-100 LOC)

```lean
-- Definición actual (EMatchSpec:58-69):
def SameShapeSemantics : Prop :=
  ∀ (op₁ op₂ : Op) (env : Nat → Val) (v₁ v₂ : EClassId → Val),
    sameShape op₁ op₂ = true →
    (∀ (i : Nat) (h₁ : i < (NodeOps.children op₁).length)
        (h₂ : i < (NodeOps.children op₂).length),
      v₁ ((NodeOps.children op₁)[i]) = v₂ ((NodeOps.children op₂)[i])) →
    NodeSemantics.evalOp op₁ env v₁ = NodeSemantics.evalOp op₂ env v₂
```

**Estrategia de prueba**: Derivar de `evalOp_ext` (NodeSemantics axiom) + `sameShape_children_length` (ya probado).

- `evalOp_ext` dice: si `∀ c ∈ children op, v₁ c = v₂ c`, entonces `evalOp op env v₁ = evalOp op env v₂`
- Pero SSS compara DISTINTOS ops (`op₁ ≠ op₂`), no solo distintas valuaciones
- Necesita: `sameShape op₁ op₂ = true → evalOp op₁ env v = evalOp op₂ env v` (para misma v)
- Esto NO se sigue solo de evalOp_ext — necesita un axioma adicional o una definición más fuerte de sameShape

**Opciones**:
- **Opción A**: Agregar `evalOp_sameShape` como axiom de NodeSemantics
- **Opción B**: Refinar `sameShape` para que implique `op₁.mapChildren id = op₂.mapChildren id` (misma estructura, solo children difieren)
- **Opción C**: Probar que `sameShape op₁ op₂ = true → ∃ f, op₂ = mapChildren f op₁` y usar evalOp_mapChildren

La Opción C es la más limpia: usa axiomas existentes (`evalOp_mapChildren` de NodeSemantics).

### A.2 ematchF_substitution_bounded (estimado: 40-80 LOC)

```lean
-- Hipótesis inline en TranslationValidation:195-199:
(hematch_bnd : ∀ (g' : EGraph Op) (rule : PatternSoundRule Op Val),
  rule ∈ rules → PostMergeInvariant g' →
  ∀ (classId : EClassId), classId < g'.unionFind.parent.size →
  ∀ σ ∈ ematchF fuel g' rule.rule.lhs classId,
  ∀ pv id, σ.get? pv = some id → id < g'.unionFind.parent.size)
```

**Estrategia**: Inducción sobre Pattern + fuel en ematchF.

- ematchF para `patVar pv`: σ.extend pv classId → id = classId < g.uf.size ✓
- ematchF para `node skelOp subpats`: foldl sobre children, cada sub-ematch produce σ' que extiende σ
  - Por IH: cada sub-σ es acotada
  - Extension preserva bounds (nuevos bindings son IDs del grafo)
- ematchF es **read-only** (no muta g) → bounds constantes durante recursión

**Lema auxiliar necesario**: `matchChildren_bounded` — si matchChildren produce σ, todos los IDs en σ están acotados.

### A.3 InstantiateEvalSound (estimado: 150-250 LOC)

```lean
-- Definición actual (EMatchSpec:500-517):
def InstantiateEvalSound (Op : Type) (Val : Type) ... (env : Nat → Val) : Prop :=
  ∀ (fuel : Nat) (g : EGraph Op) (pat : Pattern Op) (subst : Substitution) (v : EClassId → Val),
    ConsistentValuation g env v → PostMergeInvariant g → SemanticHashconsInv g env v →
    AllDistinctChildren pat →
    (∀ pv id, subst.get? pv = some id → id < g.unionFind.parent.size) →
    ∀ id g', instantiateF fuel g pat subst = some (id, g') →
    ∃ v', ConsistentValuation g' env v' ∧ PostMergeInvariant g' ∧ SemanticHashconsInv g' env v' ∧
      id < g'.unionFind.parent.size ∧ g.unionFind.parent.size ≤ g'.unionFind.parent.size ∧
      (∀ i, i < g.unionFind.parent.size → v' i = v i) ∧
      v' (root g'.unionFind id) = Pattern.eval pat env (substVal v g.unionFind subst)
```

**Estrategia**: Inducción sobre Pattern (fuel decrece, estructura recursiva).

**Caso patVar pv**:
- `instantiateF fuel g (.patVar pv) subst` = lookup subst pv → some (id, g) (g unchanged)
- v' = v (grafo no cambia)
- `v'(root g.uf id) = v(root g.uf id)` por CV
- `Pattern.eval (.patVar pv) env (substVal v g.uf subst) = substVal v g.uf subst pv = v(root g.uf id)` por definición
- **Trivial**: ~20 LOC

**Caso node skelOp subpats**:
- `instantiateF fuel g (.node skelOp subpats) subst` hace foldl sobre subpats:
  1. Para cada subpat: `instantiateF (fuel-1) g_i subpat subst` → `(childId_i, g_{i+1})`
  2. Reconstruye: `skelOp.mapChildren (fun j => childIds[j])`
  3. Llama `g_final.add reconstructedNode` → `(resultId, g')`
- Threading existencial: cada step produce v_i con agreement
- `add_node_consistent` (ya probado) da: `∃ v', CV g' env v' ∧ v'(root g'.uf resultId) = evalOp reconstructedNode env v'`
- Necesita SameShapeSemantics para conectar `evalOp reconstructedNode` con `Pattern.eval (.node skelOp subpats)`
- **Complejo**: ~130-230 LOC (foldl induction + add + threading)

**Piezas existentes reutilizables**:
- `instantiateF_preserves_addExprInv` (SaturationSpec:136) — preserva AddExprInv
- `instantiateF_preserves_consistency` (SaturationSpec:233) — preserva CV + PMI (PARCIAL)
- `add_node_consistent` (SemanticSpec:428) — add preserva CV
- `processClass_shi_combined` (SemanticSpec:1168) — patrón de foldl + threading

---

## Appendix B: Definiciones clave del código actual

### sameShape (EMatch.lean:41-45)
```lean
def sameShape [NodeOps Op] [BEq Op] (op₁ op₂ : Op) : Bool :=
  NodeOps.mapChildren (fun _ => (0 : EClassId)) op₁ ==
  NodeOps.mapChildren (fun _ => (0 : EClassId)) op₂
```

### instantiateF (SaturationSpec.lean:42-66)
```lean
def instantiateF [NodeOps Op] [BEq Op] [Hashable Op] (fuel : Nat) (g : EGraph Op)
    (pat : Pattern Op) (subst : Substitution) : Option (EClassId × EGraph Op) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match pat with
    | .patVar pv => subst.get? pv |>.map (·, g)
    | .node skelOp subPats =>
      let result := subPats.foldl (init := some ([], g)) fun acc subPat =>
        acc.bind fun (childIds, gAcc) =>
          (instantiateF fuel gAcc subPat subst).map fun (childId, gNew) =>
            (childIds ++ [childId], gNew)
      result.bind fun (childIds, gFinal) =>
        let newOp := NodeOps.replaceChildren skelOp childIds
        some (gFinal.add ⟨newOp⟩)
```

### ematchF (SaturationSpec.lean:290-322)
```lean
def ematchF [NodeOps Op] [BEq Op] [Hashable Op] (fuel : Nat) (g : EGraph Op)
    (pat : Pattern Op) (classId : EClassId) : List Substitution :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    match pat with
    | .patVar pv => [Substitution.extend .empty pv classId]
    | .node skelOp subPats =>
      let rootId := root g.unionFind classId
      match g.classes.get? rootId with
      | none => []
      | some eclass =>
        eclass.nodes.toList.filterMap fun node =>
          if sameShape node.op skelOp then
            let childPairs := (NodeOps.children node.op).zip
              (subPats.map fun subPat => (subPat, ·))  -- simplified
            matchChildren fuel g childPairs .empty
          else none
```

---

## Appendix C: Metrics actuales (corregidas por autopsy)

| Métrica | README dice | Actual (autopsy) | Delta |
|---------|:-----------:|:----------------:|:-----:|
| Teoremas | 218 | 226 | +8 |
| LOC | 7,748 | 6,899 | -849 |
| Sorry | 0 | 0 | = |
| Axiomas | 0 | 0 | = |
| Archivos Lean | 20 | 22 | +2 |
| Hipótesis no descargadas en pipeline | 0 (claimed) | 3 | +3 |
