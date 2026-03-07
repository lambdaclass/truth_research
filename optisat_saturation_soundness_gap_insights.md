# Insights: Cerrar el Gap de Soundness en Saturation (OptiSat)

**Fecha**: 2026-02-23
**Dominio**: lean4
**Estado del objeto**: upgrade (cerrar gap en proyecto existente v0.1.0)

## 1. Analisis del Objeto de Estudio

OptiSat (v0.1.0, 181 teoremas, 0 sorry, 5,327 LOC) es un motor generico de equality saturation verificado en Lean 4, parametrizado por typeclasses (NodeOps, NodeSemantics, Extractable). Tiene una cadena de soundness casi completa:

```
find_preserves_roots (UnionFind) ✓
  → merge_consistent (SemanticSpec) ✓
    → [GAP] sound_rule_preserves_consistency (NO EXISTE)
      → computeCostsF_preserves_consistency ✓
        → extractF_correct / extractILP_correct ✓
          → optimization_soundness_greedy / ilp ✓
```

**El gap**: No existe prueba de que el loop de saturacion (aplicar reglas + rebuild) preserva `ConsistentValuation`. Los end-to-end theorems ASUMEN CV como hipotesis. El README presenta la cadena como cerrada.

**Piezas faltantes (3, en orden de dependencia)**:
1. `SoundRewriteRule` typeclass — adaptar patron de SuperTensor-lean's `SoundTensorRule`
2. `applyRule_preserves_consistent` theorem — conectar merge_consistent con aplicacion de reglas
3. `saturate_preserves_consistent` theorem — induccion sobre el loop

**Inventario de codigo reutilizable entre proyectos**:

| Pieza | amo-lean | SuperTensor-lean | optisat |
|---|---|---|---|
| Regla con prueba embebida | VerifiedRule (placeholder) | SoundTensorRule (real) | No existe |
| Teoremas de reglas concretas | 24 thms sobre eval | 3 demo rules con prueba | No existe |
| ConsistentValuation | No | No | 40 theorems |
| merge preserva equiv | CoreSpec structural | merge_creates/preserves_equiv | merge_consistent (semantico) |
| saturate preserva CV | No | No | Placeholder (True) |

## 2. Lecciones Aplicables

### Lecciones criticas (Top 5)

| ID | Titulo | Aplicacion directa |
|---|---|---|
| **L-311** | Transparent Soundness Contract: Three-Part Invariant | Formular saturate como: fuel bound + result CV + frame property |
| **L-369** | Explicit Invariants for State-Passing Recursion | Threading de CV a traves del loop de saturacion |
| **L-222** | PostMergeInvariant pattern | Si applyRule rompe EGraphWF, factorizar invariante parcial |
| **L-234** | AddExprInv — invariante debil para induccion recursiva | Factorizar sub-invariante que SI se preserva en paso recursivo |
| **L-310** | End-to-End Pipeline via Generic Typeclasses | SoundRewriteRule como typeclass permite O(n+m) |

### Lecciones secundarias relevantes

| ID | Titulo | Uso |
|---|---|---|
| L-257 | ExtractableSound as standalone Prop | Separar interface operacional de obligacion de verificacion |
| L-305 | Nested induction (structural + fuel) | Induccion exterior en iteraciones + interior en fuel |
| L-243 | Generalise IH early | Estado generalizado como argumento IH |
| L-148 | foldl_invariant con membership | Para loop sobre reglas: necesitamos `rule ∈ rules` |
| L-253 | Recursive typeclass circular reference | NO definir SoundRewriteRule con auto-referencia |
| L-338 | Fuel bounds: max not sum | Componer fuel de pasos via max |
| L-244 | ResultForm as invariant, not precondition | CV como invariante derivado del loop, no precondicion |

### Anti-patrones a evitar

1. **Invariante monolitica en loop**: No intentar preservar EGraphWF completo en cada paso de saturacion. Factorizar (L-222).
2. **IH no generalizada**: Si CV depende de `v` (valuacion), generalizar `v` en la IH (L-243).
3. **Typeclass self-reference**: No definir SoundRewriteRule referenciandose a si mismo (L-253).
4. **Probar forma del resultado como precondicion**: CV es invariante derivado, no precondicion (L-244).

## 3. Bibliografia Existente Relevante

### Documentos clave en biblioteca local

| Documento | Carpeta | Aporte |
|---|---|---|
| **Suciu: Semantic Foundations of EqSat (ICDT 2025)** | tensor-optimization | Primera fundamentacion semantica rigurosa. Tree automata + chase connection. |
| **Rossel: Lean-Egg (POPL 2026)** | criptografia/zk-circuitos | Unica integracion eqsat + Lean 4. Trust model: egg busca, kernel verifica. |
| **Rossel: EqSat Tactic Thesis (2024)** | criptografia/zk-circuitos | Detalle de encoding, binders, trust boundary. |
| **Stevens: Verified Union-Find-Explain (2025)** | criptografia/zk-circuitos | Formalizacion Isabelle de UF+Explain. Stepping stone a CC verificado. |
| **Flatt: Small Proofs from CC (FMCAD 2022)** | criptografia/zk-circuitos | Proof certificates, DAG optimization, egg impl. |
| **Willsey: egg (POPL 2021)** | egraphs-treewidth | Rebuilding, e-class analyses, congruence closure. |

### Gaps bibliograficos

1. **CRITICO**: No existe mecanizacion (Lean/Coq/Isabelle) de "equality saturation preserva equivalencia semantica"
2. **CRITICO**: No existe typeclass SoundRewriteRule generico en ningun prover
3. **MEDIO**: CC verificado solo en Isabelle (Stevens), no en Lean 4
4. **MEDIO**: Rebuilding preserva congruencia — no formalizado en ningun trabajo

## 4. Estrategias y Decisiones Previas

### Estrategias ganadoras

| Estrategia | Proyecto | Resultado |
|---|---|---|
| 3-tier invariant system | VR1CS/OptiSat | Permite probar soundness incremental sin bloquear |
| ConsistentValuation como Prop central | OptiSat | 40 thms, pivot de toda la cadena de soundness |
| Fuel-based saturation | VR1CS/OptiSat | Evita well-founded opacity (Lean 4.19+) |
| De-risk teorema critico ANTES | OptiSat | merge_consistent primero, resto compone |
| Translation Validation (Path B) | SuperTensor | Fallback: verificar resultado, no algoritmo |

### Benchmarks de referencia

| Metrica | OptiSat v0.1.0 | Target post-gap |
|---|---|---|
| Teoremas | 181 | ~190-195 |
| LOC | 5,327 | ~5,800-6,200 |
| Sorry | 0 | 0 |
| Axiomas | 0 | 0 |
| Compilacion | ~20s | <30s |

## 5. Nueva Bibliografia Online

### Papers encontrados

| Paper | Venue | Aporte al gap |
|---|---|---|
| **Suciu et al.: Semantic Foundations of EqSat** | ICDT 2025 | Teoria semantica que fundamenta soundness (no mecanizado) |
| **Rossel et al.: lean-egg** | POPL 2026 | Trust model Lean+egg: kernel verifica, egg no verificado |
| **Stevens & Ghidini: Verified UF-Explain** | arXiv 2025 | Formalizacion Isabelle, stepping stone a CC |
| **Leray et al.: The Rewster** | ITP 2024 | Patron de certificacion de rewrite rules en Coq/MetaCoq |
| **Arora et al.: TensorRight** | POPL 2025 | Verificacion de tensor rewrites via denotational semantics + SMT |
| **lean-smt** | ITP 2025 | Proof reconstruction de CC via cvc5 en Lean |

### Hallazgo clave

**Nadie ha mecanizado la prueba de que equality saturation preserva equivalencia semantica.** Si lo logramos en optisat, seria el primero.

## 6. Sintesis de Insights

### Hallazgos clave (Top 8)

1. **El gap es original**: No existe mecanizacion de saturation soundness en ningun prover. Cerrar esto en Lean 4 seria contribucion novedosa.

2. **SuperTensor tiene el patron correcto**: `SoundTensorRule` con campo `sound : ∀ env, lhs.eval env = rhs.eval env` es exactamente lo que necesitamos, adaptado a generico.

3. **La pieza mas dificil es applyRule_preserves_consistent**: Conecta ematch (encuentra patron) + instanciacion (crea nodo rhs) + merge (unifica clases). Requiere probar que si `lhs.eval = rhs.eval` y ematch encuentra lhs en el e-graph, entonces mergear con rhs preserva CV.

4. **saturate_preserves_consistent es induccion directa**: Una vez que tenemos applyRule_preserves_consistent, el loop es induccion en fuel con IH generalizada sobre el estado del e-graph.

5. **Necesitamos factorizar el paso de saturacion**: applyRule internamente hace (1) ematch → matches, (2) instanciate → new nodes, (3) merge → unify classes. Cada sub-paso necesita su preservation lemma.

6. **El approach de lean-egg (verificar resultado, no algoritmo) es el fallback**: Si la prueba directa es intratable, podemos adoptar translation validation (como SuperTensor).

7. **Lecciones L-311 y L-369 son non-negotiable**: Three-part contract + explicit invariant threading son prerequisitos para que la prueba cierre.

8. **El esfuerzo estimado es acotado**: ~500-800 LOC nuevos, 8-15 teoremas, basado en benchmarks de merge_consistent (~40 LOC) y extractF_correct (~60 LOC).

### Riesgos identificados

| Riesgo | Severidad | Mitigacion |
|---|---|---|
| ematch correctness: probar que matches son validos | ALTA | De-risk con sketch ANTES de teorema completo |
| instanciate preserva estructura | MEDIA | Puede requerir AddExprInv parcial (L-234) |
| Valuacion v cambia post-merge | MEDIA | Existential ∃ v' (no preservar v exacto) |
| Rebuild post-merge rompe CV | MEDIA | Ya tenemos merge_consistent; rebuild restaura |
| Scope creep: probar ematch completeness | BAJA | Solo necesitamos soundness, no completeness |

### Recomendaciones para planificacion

1. **De-risk**: Sketch de `applyRule_preserves_consistent` PRIMERO (nodo critico)
2. **Factorizar**: `SoundRewriteRule` → `ematch_sound` → `instanciate_preserves` → `merge_consistent` → `applyRule_preserves_consistent` → `saturate_preserves_consistent`
3. **Existential sobre v**: `saturate_preserves_consistent` deberia concluir `∃ v', ConsistentValuation g' env v'` (no preservar el mismo `v`)
4. **Actualizar TranslationValidation**: Reemplazar hipotesis sueltas por `SoundRewriteRule` en optimization_soundness
5. **Actualizar README**: Cerrar la cadena de soundness o documentar honestamente el gap

### Recursos prioritarios

1. **Suciu et al. (ICDT 2025)** — fundamentacion semantica
2. **L-311** — Three-part soundness contract
3. **L-369** — Explicit invariant threading
4. **L-222 + L-234** — Invariant factorization
5. **SuperTensor SoundTensorRule** — patron de diseno para typeclass
