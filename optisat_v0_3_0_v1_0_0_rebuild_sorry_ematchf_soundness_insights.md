# Insights: OptiSat v0.3.0 + v1.0.0 — Rebuild Sorry + ematchF Soundness

**Fecha**: 2026-02-23
**Dominio**: lean4
**Estado del objeto**: upgrade

## 1. Análisis del Objeto de Estudio

### Resumen

OptiSat v0.2.0 es un motor de equality saturation formalmente verificado en Lean 4, parametrizado por typeclasses genéricas (`NodeOps`, `NodeSemantics`, `Extractable`). Con 188 teoremas, 6,538 LOC, y 1 sorry aislado, el proyecto aborda dos objetivos:

1. **v0.3.0**: Cerrar el único sorry en `rebuildStepBody_preserves_cv` relajando las precondiciones de `processClass_consistent` y `mergeAll_consistent` de `WellFormed` a `PostMergeInvariant`.
2. **v1.0.0**: Implementar Opción B — definir `Pattern.eval` (semántica denotacional de patrones) y probar `ematchF_sound`, eliminando la assumption `PreservesCV` del usuario y cerrando 100% del gap de soundness.

### Keywords

equality saturation, e-graph, ConsistentValuation, PostMergeInvariant, WellFormed, rebuild correctness, Pattern.eval, denotational semantics, e-matching soundness, ematchF, SoundRewriteRule, PreservesCV, fuel-based termination, congruence closure, forward preservation, foldl invariant

### Estado actual

- **v0.2.0**: 188 theorems, 6,538 LOC, 1 sorry (`rebuildStepBody_preserves_cv`), 0 axiomas
- **Cadena de soundness**: Cerrada vía `PreservesCV` assumption (Opción A). El usuario provee proof de que cada regla preserva CV.
- **Sorry**: Aislado en rebuild path. `processClass_consistent` y `mergeAll_consistent` requieren `WellFormed g.unionFind`, no disponible en estados intermedios post-merge.

### Gaps identificados

| Gap | Descripción | Versión |
|-----|-------------|---------|
| G1 | `processClass_consistent` requiere `WellFormed` pero rebuild opera bajo `PostMergeInvariant` | v0.3.0 |
| G2 | `mergeAll_consistent` requiere `WellFormed` + `∀ p ∈ merges, v p.1 = v p.2` + bounds | v0.3.0 |
| G3 | `Pattern.eval` no existe — no hay semántica denotacional de patrones | v1.0.0 |
| G4 | `PreservesCV` es assumption del usuario, no derivado internamente | v1.0.0 |
| G5 | No hay `ematchF_sound` — vínculo ematch↔semántica no probado | v1.0.0 |

### Recursos hermanos reutilizables

| Proyecto | Recurso | Aplicación |
|----------|---------|------------|
| **vr1cs-lean** | `processClass_consistent` (SemanticSpec:478) | Template para v0.3.0 — necesita relajar WellFormed |
| **vr1cs-lean** | `mergeAll_consistent` (SemanticSpec:1159) | Template para v0.3.0 — necesita relajar WellFormed |
| **vr1cs-lean** | `instantiateF`, `ematchF` (SemanticSpec:1656-1758) | Templates para v1.0.0 — versiones totales con fuel |
| **SuperTensor-lean** | `SoundTensorRule` + `TranslationValidation` (21 thms) | Patrón para `SoundRewriteRule` — `sound` field embebido |
| **SuperTensor-lean** | CircuitBijectionProof (N2.1-N2.5) | Patrón de threading ∃v' a través de recursión |

**Hallazgo clave de vr1cs-lean**: No hay `Pattern.eval` ni `ematchF_sound`. VR1CS usa el mismo patrón `PreservesCV` que OptiSat v0.2.0. La Opción B es genuinamente NUEVA — no es un port.

---

## 2. Lecciones Aplicables

### Lecciones críticas (Top 10)

| ID | Título | Relevancia | Aplicación |
|----|--------|------------|------------|
| **L-222** | PostMergeInvariant — Relajar Invariantes Durante Mutación | CRÍTICA | Patrón exacto para v0.3.0: factorizar EGraphWF → PMI para rebuild |
| **L-234** | AddExprInv — Invariante Débil para Inducción Recursiva | CRÍTICA | Pattern.eval probablemente necesita invariante débil similar |
| **L-235** | add_node_consistent — Workhorse Universal | CRÍTICA | ematchF_sound necesita workhorse hit/miss + threading ∃v' |
| **L-237** | Forward Preservation Chain en Recursión | CRÍTICA | Threading de valuaciones existenciales a través de ematchF recursivo |
| **L-148** | foldl_invariant_mem — Membership en Paso | CRÍTICA | rebuild es foldl sobre classes — invariantes dependen de cada class |
| **L-138** | NUNCA Diferir Nodos Fundacionales como Debt | CRÍTICA | Pattern.eval y rebuild_preserves_cv son FUNDACIONALES |
| **L-134–L-137** | Framework DAG de De-Risking | CRÍTICA | Orden topológico obligatorio antes de atacar |
| **L-236** | nodeEval_canonical — Puente Semántico | ALTA | Puente entre pattern original y canonicalizado en ematch |
| **L-142** | Equation Lemmas para Unfold Selectivo | ALTA | Pattern.eval y ematchF tendrán múltiples branches |
| **L-243** | Generalise Induction Hypothesis Early | ALTA | IH de instantiateF/ematchF necesita generalización temprana |

### Lecciones por categoría (78 ALTA + 42 MEDIA)

**Invariantes y preservación**: L-222, L-234, L-230, L-223, L-229, L-311, L-244, L-315, L-369
**Inducción y recursión**: L-148, L-231, L-218, L-227, L-078, L-158, L-205, L-243, L-284, L-288, L-305
**Semántica y soundness**: L-235, L-236, L-237, L-311, L-256, L-297, L-337
**Fuel-based**: L-284, L-288, L-292, L-322, L-325, L-338
**Técnicas de proof**: L-142, L-023, L-099, L-238, L-239, L-240, L-241, L-210, L-150
**Bridge lemmas**: L-146, L-315, L-321, L-336, L-368
**HashMap**: L-224, L-228, L-240, L-220, L-221
**Planificación**: L-134, L-135, L-136, L-137, L-138, L-114, L-216

### Anti-patrones a evitar

| Anti-patrón | Lección | Descripción |
|-------------|---------|-------------|
| Diferir fundacionales | L-138, L-114 | Pattern.eval es FUNDACIONAL — probar PRIMERO, no último |
| Invariante monolítico en loop | L-222 | NO intentar preservar EGraphWF completo en rebuild — factorizar |
| foldl sin membership | L-148 | Cuando P(f b a) depende de a, usar foldl_invariant_mem |
| IH no generalizada | L-243 | Generalizar estado en IH: `∀ acc, P acc → ...` |
| simp + match en funciones complejas | L-099 | Usar split o equation lemmas, no simp directo |
| root_idempotent con root como argumento | L-225 | Pasar id original a root_idempotent, NO root(id) |
| Sorry como debt | L-140 | Statement falso con sorry = bug, no deuda técnica |
| Scope creep: probar completeness | — | Solo soundness de ematch. Completeness es optimization, no correctness |

### Patrones de proof exitosos

**Patrón 1: Invariante Débil para Recursión** (L-234, L-222)
```
EGraphWF.toAddExprInv → AddExprInv preservado recursivamente → restaurar EGraphWF
```

**Patrón 2: Forward Preservation Chain** (L-237)
```
IH(a): v1(idA) = a.eval, hfp1 : v1(i) = v(i) para i < g.uf.size
IH(b): v2(idB) = b.eval, hfp2 : v2(i) = v1(i) para i < g1.uf.size
Composición: (hfp3 _ bound).trans ((hfp2 _ bound).trans (hfp1 _ bound))
```

**Patrón 3: Workhorse Universal con Split** (L-235)
```lean
simp only [EGraph.add]; split
· -- hit case: use v
· -- miss case: simp only [UnionFind.add]; ...
```

**Patrón 4: Contrato Merge-Rebuild** (L-222, L-230)
```
WF → merge → PMI → processClass(PMI→PMI) → mergeAll(PMI→PMI) → rebuild restores WF
```

**Patrón 5: foldl con Membership** (L-148)
```lean
theorem foldl_invariant_mem (l : List α) (f : β → α → β) (init : β)
    (P : β → Prop) (h_init : P init)
    (h_step : ∀ b a, a ∈ l → P b → P (f b a)) :
    P (l.foldl f init)
```

---

## 3. Bibliografía Existente Relevante

### Documentos clave (en biblioteca local)

| Documento | Carpeta | Relevancia |
|-----------|---------|------------|
| **Semantic Foundations of EqSat** (Suciu 2025) | tensor-optimization | CRÍTICA — tree automata model, fixpoint semantics |
| **egg: Fast and Extensible EqSat** (Willsey 2021) | egraphs-treewidth | ALTA — Theorem 3.1 sobre rebuild correctness (informal) |
| **lean-egg POPL 2026** (Rossel et al.) | verificacion | CRÍTICA — encoding Lean↔e-graph, proof reconstruction |
| **Efficient E-Matching** (de Moura & Bjorner 2007) | verificacion | CRÍTICA — definición formal de e-matching problem |
| **Relational E-Matching** (Zhang et al. 2022) | verificacion | ALTA — e-matching como join relacional |
| **CC in Intensional Type Theory** (Selsam 2016) | verificacion | ALTA — CC proof-producing en Lean |
| **Colored E-Graph** (Singher 2023) | verificacion | MEDIA — invariantes bajo condiciones |
| **ROVER** (Coward 2024) | zk-circuitos | MEDIA — verified e-graph rewriting pipeline |
| **Proof-Producing CC** (Nieuwenhuis 2005) | zk-circuitos | MEDIA — proof certificates para CC |
| **Small Proofs from CC** (Flatt 2022) | zk-circuitos | MEDIA — certificates compactos |

### Gaps bibliográficos

1. **No existe formalización mecanizada de e-matching soundness** en ningún proof assistant
2. **No existe prueba formal de rebuild correctness** — solo Theorem 3.1 de egg (informal)
3. **No existe Pattern.eval formalizado** — Suciu 2025 da tree automata model pero nivel matemático
4. **OptiSat sería el primero** en verificar formalmente el motor completo de equality saturation

---

## 4. Estrategias y Decisiones Previas

### Estrategias ganadoras

| Estrategia | Proyecto | Resultado |
|------------|----------|-----------|
| **3-Tier Invariant System** (EGraphWF→PMI→AddExprInv) | VR1CS, SuperTensor | Permite probar soundness sin invariantes monolíticos |
| **ConsistentValuation como Prop Pivot** | OptiSat, VR1CS | 40+ thms threading CV explícitamente |
| **Fuel-Based Saturation** | VR1CS, Trust-Lean | Terminación probada sin opacidad de well-founded |
| **De-Risk Teorema Crítico ANTES** | SuperTensor F11 | CircuitBijectionProof (5,490 LOC) pasó QA |
| **Translation Validation como Fallback** | SuperTensor, VR1CS | 21 congruence thms como respaldo |
| **∃v' existencial (no preservación exacta)** | OptiSat v0.2.0 | Permite que rebuild cambie la valuación |

### Decisiones arquitecturales aplicables

| Decisión | Justificación |
|----------|---------------|
| `SoundRewriteRule` como structure con `sound` field | Permite reuso cross-proyecto (SuperTensor patrón) |
| `applyRule_preserves_consistent` como CRÍTICO | ematch+instantiate+merge es donde reside complejidad |
| Separar CV de EGraphWF | CV semántica local ≠ WF estructural global |
| Solo probar soundness de ematch, NO completeness | Completeness es optimization, no correctness |

### Benchmarks de referencia

| Métrica | VR1CS v1.2.0 | SuperTensor v3.1 | OptiSat v0.2.0 | Target v1.0.0 |
|---------|:---:|:---:|:---:|:---:|
| Teoremas | 204 | 310+ | 188 | ~210-220 |
| LOC | 4,664 | 5,490+ | 6,538 | ~7,500-8,000 |
| Sorry | 0 | 0 | 1 | 0 |
| Thm/KLOC | 21.2 | — | 28.8 | ~28 |

### Cadena de soundness target (v1.0.0)

```
find_preserves_roots (UnionFind, 44 thms)
  → add_node_consistent (CoreSpec)
    → merge_consistent (SemanticSpec, 40 thms)
      → sound_rule_preserves_consistency (SoundRule)
        → instantiateF_preserves_consistency (SaturationSpec)
          → ematchF_sound (NEW v1.0.0)                          ← NUEVO
            → applyRuleF_preserves_cv_internal (NEW v1.0.0)     ← NUEVO (sin PreservesCV assumption)
              → rebuildStepBody_preserves_cv (v0.3.0)           ← CERRAR SORRY
                → saturateF_preserves_consistent (SaturationSpec)
                  → computeCostsF_preserves_consistency (SemanticSpec)
                    → extractF_correct / extractILP_correct
                      → full_pipeline_soundness_greedy (TranslationValidation)
```

---

## 5. Nueva Bibliografía Encontrada

### Papers descargados (5)

| # | Paper | Path | Aporte clave |
|---|-------|------|-------------|
| 1 | **Efficient E-Matching for SMT Solvers** (de Moura & Bjorner, CADE 2007) | `biblioteca/verificacion/demoura-bjorner-efficient-ematching-smt-solvers-cade-2007.pdf` | Definición formal del e-matching problem: encontrar θ tal que E⊨t~θ(p). Referencia canónica para especificación de `ematchF_sound`. |
| 2 | **Relational E-Matching** (Zhang et al., POPL 2022) | `biblioteca/verificacion/zhang-wang-willsey-tatlock-relational-ematching-popl-2022.pdf` | E-matching como join relacional con garantía worst-case optimal. Semántica declarativa alternativa para Pattern.eval. |
| 3 | **Congruence Closure in Intensional Type Theory** (Selsam & de Moura, IJCAR 2016) | `biblioteca/verificacion/selsam-demoura-congruence-closure-intensional-type-theory-ijcar-2016.pdf` | CC proof-producing formalizado en Lean. Directamente aplicable a rebuild correctness y ConsistentValuation preservation. |
| 4 | **Colored E-Graph** (Singher & Itzhaky, 2023) | `biblioteca/verificacion/singher-itzhaky-colored-egraph-equality-reasoning-conditions-2023.pdf` | Múltiples relaciones de congruencia en un e-graph. Relevante para invariantes semánticos bajo condiciones. |
| 5 | **lean-egg: Equality Saturation Tactic for Lean** (Rossel et al., POPL 2026) | `biblioteca/verificacion/rossel-goens-lean-egg-equality-saturation-tactic-lean-popl-2026.pdf` | Encoding Lean↔e-graph, proof reconstruction. La referencia más directa para interfaz Lean 4 ↔ equality saturation. |

### Papers ya existentes en biblioteca

egg (Willsey 2021), Suciu 2025 (Semantic Foundations), Rossel 2024 (Bridging Syntax/Semantics), Nieuwenhuis 2005/2007 (CC), ROVER (Coward 2024), egglog (Zhang 2023), Koehler 2024 (Guided EqSat).

### Hallazgo clave

**OptiSat opera en espacio genuinamente novedoso**: ninguna formalización existente mecaniza la soundness de e-matching ni la corrección de rebuild. lean-egg usa egg como caja negra y reconstruye proofs a posteriori. OptiSat verificaría el motor internamente — sería el primero.

---

## 6. Insights de Nueva Bibliografía

### 6.1 de Moura & Bjorner 2007 — Especificación formal de e-matching

**Insight 1 — Semántica abstracta de match (Fig. 1, p.4)**:
```
match(x, t, S) = {β ∪ {x→t} | β∈S, x∉dom(β)} ∪ {β | β∈S, find(β(x))=find(t)}
match(f(p1,...,pn), t, S) = ∪_{f(t1,...,tn)∈class(t)} match(pn,tn,...,match(p1,t1,S))
```
Esta es **exactamente** la especificación denotacional que OptiSat necesita para `Pattern.eval`. La estructura recursiva `match`/`matchPairs` de `EMatch.lean:47-75` sigue esta misma forma. Para definir `Pattern.eval`, la clave: un patrón `node op subpats` se evalúa al valor semántico del nodo cuando la sustitución es válida.

**Insight 2 — Instrucción `compare` para variables repetidas (p.4-5)**. Cuando una variable aparece múltiples veces, la máquina verifica `find(reg[i]) = find(reg[j])`. Corresponde directamente a `Substitution.extend` de OptiSat: `if existingId == id then some subst else none`. La soundness de esta verificación es crítica para `ematchF_sound`.

### 6.2 Zhang et al. 2022 — Relational E-Matching

**Insight 3 — Separación structural/equality constraints (p.10)**. El paper distingue explícitamente entre:
- **Restricciones estructurales**: del árbol del patrón (cada nodo matchea por shape)
- **Restricciones de igualdad**: de variables repetidas (sustitución consistente)

Sugiere **factorizar la prueba de `ematchF_sound` en dos lemmas**: uno para shape matching, otro para variable consistency.

**Insight 4 — Corrección via conjunctive queries (Sec. 3.2)**. Cada sustitución devuelta por ematchF corresponde a una tupla de la query conjuntiva inducida por el patrón. La prueba de soundness puede proceder mostrando que cada sustitución satisface la query.

### 6.3 Selsam & de Moura 2016 — CC en Intensional Type Theory

**Insight 5 (CRÍTICO para v0.3.0) — UF WellFormed se mantiene durante TODO el rebuild**. El paper lista 4 invariantes de CC que se mantienen **siempre**, incluso cuando la congrtable (≈hashcons) está temporalmente inconsistente. La clave: `processeq` (≈processClass) solo hace unions, y las unions preservan WellFormed. Esto es exactamente lo que necesitamos:

> `rebuildStepBody_preserves_cv` necesita mostrar que CV se preserva durante rebuild. Los merges producidos por processClass son semánticamente válidos (`processClass_merges_semantically_valid`, SemanticSpec:544). `mergeAll_consistent` (SemanticSpec:654) necesita `WellFormed` — y **WellFormed SÍ se mantiene** porque processClass preserva UF.WellFormed (vía `processClass_preserves_pmi`, CoreSpec:924, que incluye UF WF).

**El argumento central para cerrar el sorry**: lo que falla durante rebuild NO es WellFormed del UF, sino hashcons consistency. Pero `mergeAll_consistent` solo necesita UF WellFormed + bounds + merge validity — NO necesita hashcons_consistent.

**Insight 6 — Separación congrtable vs union-find (p.8-9)**. La congrtable puede estar inconsistente sin afectar la corrección de las unions. `CONGRUENT(D, E)` solo depende de `repr` (union-find), no de congrtable. En OptiSat: `ConsistentValuation` depende de UF roots y semántica de nodos, NO de hashcons. Esto confirma que relajar `EGraphWF` → `PostMergeInvariant` (que preserva UF WF) es suficiente.

### 6.4 Singher & Itzhaky 2023 — Colored E-Graphs

**Insight 7 — Deferred rebuilding formalmente justificado (p.3, 5)**. El rebuild puede ser diferido sin afectar corrección de unions, solo completitud de congruencia. Refuerza: relajar `EGraphWF` → `PostMergeInvariant` durante rebuild es correcto.

**Insight 8 — Multi-level union-find (p.4-5)**. UF multi-nivel con UF maestro + UFs incrementales. Conceptualmente similar al diseño de 3 invariantes (EGraphWF > PMI > AddExprInv). Operaciones en nivel superior solo necesitan invariantes de ese nivel.

**Insight 9 — E-matching sin hashcons reconstruido (p.5)**. E-matching opera sobre `g.classes` directamente sin requerir `hashcons_consistent`. Confirma que `ematchF` de OptiSat es correcto incluso durante estados intermedios.

### 6.5 Rossel et al. 2026 — lean-egg

**Insight 10 — Encoding de patrones (Sec. 4.1-4.3)**. `[[x]] := ?i_x` es directamente análogo a `Pattern.patVar pv`. `Pattern.eval` que OptiSat necesita es: la semántica del patrón es el valor semántico del término instanciado.

```lean
-- Definición sugerida (de análisis cruzado papers 1+5):
def Pattern.eval [NodeSemantics Op Val] (pat : Pattern Op)
    (env : Nat → Val) (v : EClassId → Val) (subst : Substitution) : Option Val :=
  match pat with
  | .patVar pv => subst.lookup pv |>.map v
  | .node skelOp subpats =>
    let childVals := subpats.mapM (fun p => Pattern.eval p env v subst)
    childVals.map (fun cvs => NodeSemantics.evalOp skelOp env (fun i => cvs.getD i default))
```

**Insight 11 — Conditional rewrite rules (Def. 4.9)**. `M if G => L = R` corresponde a `RewriteRule Op` con `sideCondCheck` (EMatch.lean:113-117). Ya soportado en OptiSat via `ConditionalSoundRewriteRule`.

**Insight 12 — Proof erasure justifica evalOp_ext (p.8)**. lean-egg borra proofs y type class instances. `evalOp_ext` de `NodeSemantics` (que dice que evalOp solo depende de v a través de los hijos) es la propiedad que permite esto.

### 6.6 Conceptos nuevos incorporados al grafo conceptual

33 conceptos nuevos, 31 aristas nuevas. Los más relevantes:

| Concepto | Impacto OptiSat |
|----------|-------------------|
| `relational-e-matching` | Alternativa óptima al backtracking; base formal para soundness |
| `conjunctive-queries` | Base formal para probar ematchF_sound |
| `deferred-rebuilding` | Justificación formal para relajar EGraphWF durante rebuild |
| `colored-e-graphs` | Design pattern para invariantes multi-nivel |
| `conditional-rewrite-rules` | Ya soportado via ConditionalSoundRewriteRule |
| `proof-erasure` | Justifica evalOp_ext de NodeSemantics |

### 6.7 Conexiones descubiertas

| Concepto OptiSat | ↔ | Concepto Paper | Paper |
|---------------------|---|----------------|-------|
| `PostMergeInvariant` | = | deferred-rebuilding invariant | Singher 2023 |
| `processClass_merges_semantically_valid` | = | CONGRUENT(D,E) proposition | Selsam 2016 |
| `ematchF` | = | abstract machine `match` | de Moura 2007 |
| `SoundRewriteRule.cond_preserves_cv` | = | conditional rewrite soundness | Rossel 2026 |
| `ConsistentValuation` | ≈ | semantic equivalence class property | Suciu 2025 |

---

## 7. Síntesis de Insights

### Hallazgos clave (Top 10)

1. **El sorry es cerrable con trabajo acotado** (~200-300 LOC). El insight de Selsam & de Moura 2016 (Insight 5) confirma que UF WellFormed se mantiene durante TODO el rebuild — lo que falla es hashcons_consistent, pero `mergeAll_consistent` NO lo necesita. Combinado con L-222 (PostMergeInvariant) y `processClass_preserves_pmi` (que preserva UF WF), la estrategia es clara: probar que el foldl de processClass preserva CV y acumula merges válidos/bounded, luego aplicar `mergeAll_consistent`.

2. **Opción B es genuinamente nueva investigación**. Ni vr1cs-lean, ni SuperTensor-lean, ni lean-egg, ni ningún otro proyecto tiene `ematchF_sound` mecanizado. OptiSat sería el primero en verificar internamente el motor de equality saturation. Esto es publicable.

3. **La especificación formal de ematchF_sound ya existe** (de Moura & Bjorner 2007, Insight 1): encontrar θ tal que `E ⊨ t ≈ θ(p)`. La traducción a Lean es directa — el trabajo es la prueba, no la especificación. Zhang et al. 2022 (Insight 3) sugiere factorizar la prueba en structural constraints + equality constraints.

4. **Pattern.eval tiene dos diseños posibles**:
   - **(A) Recursivo directo**: `Pattern.eval : Pattern Op → Env → (EClassId → Val) → Substitution → Option Val` con recursión estructural. Definición sugerida en Insight 10 (Rossel 2026 + de Moura 2007). Semántica: el valor del patrón es el valor semántico del término instanciado.
   - **(B) Relacional/query**: interpretar el patrón como conjunctive query sobre el e-graph (Zhang et al. 2022). Más elegante pero requiere más infraestructura.
   - **Recomendación**: Opción (A) para v1.0.0. La clave del diseño: `patVar pv` lookup en sustitución → `v(σ(pv))`; `node skelOp subpats` → `evalOp skelOp env (childVals)`.

5. **Forward Preservation Chain (L-237) es el patrón central** para ematchF_sound. Cada match recursivo produce una nueva valuación v' con forward preservation. La composición es: `(hfp_n).trans ... (hfp_2).trans (hfp_1)`.

6. **foldl_invariant_mem (L-148) es esencial** para v0.3.0. `rebuildStepBody` hace foldl sobre clases; el invariante de cada paso depende de qué clase se procesa.

7. **De-risk ematchF_sound ANTES de dependientes** (L-136, L-138). Es el nodo más crítico y más difícil. Sketch con sorry en pasos intermedios primero.

8. **Solo soundness, no completeness** (decisión arquitectural). `ematchF_sound` solo prueba que los matches encontrados son válidos. No prueba que encuentra TODOS los matches. Completeness es optimization, no correctness.

9. **La semántica de `patVar` está resuelta por los papers** (Insights 1+10). `Pattern.eval (.patVar pv) env v subst = subst.lookup pv |>.map v`. El patrón variable se evalúa al valor de la clase a la que la sustitución lo mapea. Pattern.eval recibe la sustitución como parámetro (4 args: pat, env, v, subst → Option Val).

10. **El contrato merge-rebuild (L-222, L-230) se aplica directamente a v0.3.0**:
    ```
    merge: EGraphWF → PostMergeInvariant (preserva UF.WF + ChildrenBounded + entries_valid)
    processClass: PostMergeInvariant → PostMergeInvariant (solo modifica hashcons)
    mergeAll: PostMergeInvariant + (∀ p, v p.1 = v p.2) → PostMergeInvariant
    rebuild_restores: PostMergeInvariant → EGraphWF
    ```

### Riesgos identificados

| Riesgo | Severidad | Mitigación |
|--------|-----------|------------|
| `processClass_consistent` requiere lemmas no triviales bajo PMI | MEDIA | VR1CS tiene template; factorizar en helpers |
| `Pattern.eval` semántica de patVar ambigua | ALTA | Definir claramente: patVar = lookup en sustitución, node = evalOp recursivo |
| ematchF_sound requiere inducción mutua (patrón + e-graph) | MUY ALTA | De-risk con sketch; considerar fuel como simplificación |
| mergeAll_consistent necesita `∀ p ∈ merges, v p.1 = v p.2` | MEDIA | processClass produce merges con esta propiedad (congruence) |
| Scope creep: probar completeness de ematch | BAJA | Decisión firme: solo soundness |
| Build time regression | BAJA | Monitor incremental; target <30s |

### Recomendaciones para planificación

**v0.3.0 (Fase 6: Cerrar Sorry)**:
1. Definir `processClass_consistent_weak` que use precondiciones relajadas (PMI, no WF)
2. Definir `mergeAll_consistent_weak` análogamente
3. Probar que processClass produce merges con `v p.1 = v p.2` (congruence property)
4. Cerrar `rebuildStepBody_preserves_cv` componiendo los tres
5. Verificar 0 sorry, 0 axiomas
6. Estimado: ~200-300 LOC, 5-8 teoremas nuevos

**v1.0.0 (Fase 7: ematchF Soundness)**:
1. **(FUNDACIONAL)** Definir `Pattern.eval` con semántica recursiva
2. **(FUNDACIONAL)** Probar `Pattern.eval_node_correct`: conexión con `NodeSemantics.evalOp`
3. **(CRÍTICO)** Probar `ematchF_sound`: si ematchF retorna σ, Pattern.eval bajo σ = v(classId)
4. **(CRÍTICO)** Probar `applyRuleF_preserves_cv_internal`: usando ematchF_sound + SoundRewriteRule.soundness, sin PreservesCV assumption
5. **(HOJA)** Actualizar `saturateF_preserves_consistent` para usar proof interno
6. **(HOJA)** Actualizar `full_pipeline_soundness_greedy` — eliminar PreservesCV del statement
7. Estimado: ~500-800 LOC, 10-15 teoremas nuevos

### Recursos prioritarios

1. **L-222** (PostMergeInvariant pattern) — para v0.3.0
2. **L-237** (Forward Preservation Chain) — para v1.0.0 ematchF_sound
3. **L-235** (add_node_consistent workhorse) — para Pattern.eval_correct
4. **de Moura & Bjorner 2007** (e-matching specification) — especificación de ematchF_sound
5. **Suciu 2025** (Semantic Foundations) — tree automata model para Pattern.eval
6. **L-148** (foldl_invariant_mem) — para v0.3.0 rebuild
7. **Selsam 2016** (CC in ITT) — para rebuild correctness en Lean
8. **L-142** (equation lemmas) — para control fino de Pattern.eval/ematchF proofs
9. **vr1cs-lean SemanticSpec:310-340** — template de processClass_consistent
10. **vr1cs-lean SemanticSpec:650-680** — template de mergeAll_consistent
