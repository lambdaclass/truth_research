# LambdaSat-Lean: Verified Equality Saturation Engine

## Proyecto

Motor genérico de Equality Saturation formalmente verificado en Lean 4, parametrizado por typeclasses.
Extraído y generalizado a partir de VR1CS-Lean (motor de e-graphs verificado para circuitos R1CS).

- **Dominio**: lean4
- **Toolchain**: leanprover/lean4:v4.26.0
- **Config**: lakefile.toml
- **Compilar**: `lake build`
- **Origen**: VR1CS-Lean v1.3.0 (~5,100 LOC spec, 156 teoremas, zero sorry)

## Estado Actual — v0.0.0 GENESIS

- Proyecto recién creado. Código fuente pendiente.
- **Objetivo v0.1.0**: Typeclass-parameterized e-graph engine con zero sorry
- **Meta**: ~6,000 LOC, ~156 teoremas, zero sorry, zero axiomas personalizados

### Arquitectura Target

```
LambdaSat/
├── UnionFind.lean               -- Copia directa de VR1CS (1,235 LOC, 44 thms)
├── Core.lean                    -- EGraph Op [NodeOps Op] (generalizado)
├── CoreSpec.lean                -- EGraphWF Op, PostMergeInvariant Op
├── SemanticSpec.lean            -- ConsistentValuation Op Val [NodeSemantics Op Val]
├── EMatch.lean                  -- Pattern Op, ematch genérico
├── Saturate.lean                -- saturate genérico
├── Optimize.lean                -- cost extraction, optimizeExpr
├── ILP.lean                     -- ILP types
├── ILPEncode.lean               -- E-graph → ILP encoding
├── ILPSolver.lean               -- HiGHS + B&B solver
├── ILPCheck.lean                -- Certificate checking + extraction
├── ILPSpec.lean                 -- extractILP_correct, ilp_extraction_soundness
├── ParallelMatch.lean           -- IO.asTask parallel matching
├── ParallelSaturate.lean        -- Parallel saturation loop
└── TranslationValidation.lean   -- Path B proof witnesses
```

### Typeclasses Core

```lean
class NodeOps (Op : Type) where
  children : Op → List EClassId
  mapChildren : Op → (EClassId → EClassId) → Op

class NodeSemantics (Op : Type) (Val : Type) extends NodeOps Op where
  evalOp : Op → (Nat → Val) → (EClassId → Val) → Val

class Extractable (Op : Type) (Expr : Type) (Val : Type)
    extends NodeSemantics Op Val where
  reconstruct : Op → List Expr → Option Expr
  evalExpr : Expr → (Nat → Val) → Val
  reconstruct_sound : ...
```

### Cadena de Soundness (target)

```
find_preserves_roots (UnionFind)
  → merge_consistent (Core)
    → sound_rule_preserves_consistency (SemanticSpec)
      → computeCostsF_preserves_consistency (SemanticSpec)
        → extractF_correct / extractILP_correct (Extraction)
          → optimization_soundness_pipeline (Top-level)
```

### Invariantes (3-tier design, de VR1CS-Lean)

- **EGraphWF**: Full well-formedness (antes/después de operaciones completas)
- **PostMergeInvariant**: Parcial durante merge (antes de rebuild)
- **AddExprInv**: Parcial durante addExpr (inserción recursiva)

## Proyecto Hermano

- **VR1CS-Lean**: `~/Documents/claudio/vr1cs-lean/` — instanciación para R1CS
  - Eventualmente importará LambdaSat-Lean como dependencia Lake
  - NO tocar VR1CS-Lean desde este proyecto

## Recursos del Dominio

- **Bibliografía**: `~/Documents/claudio/biblioteca/{criptografia,matematica,optimizacion}/`
- **Lecciones**: `~/Documents/claudio/lecciones/lean4/` (INDEX.md → carga selectiva)
- **Índices**: `~/Documents/claudio/biblioteca/indices/`
- **VR1CS-Lean (referencia)**: `~/Documents/claudio/vr1cs-lean/VR1CS/EGraph/`

## Skills Lean 4

| Necesidad | Skill |
|-----------|-------|
| Planificación | `/plan-project --domain lean4` |
| Búsqueda proyecto actual (LSP) | `/lean-search`, `/lean-check`, `/lean-diagnostics` |
| Búsqueda Mathlib (87K teoremas) | `/ask-dojo` |
| Estrategia de prueba (DeepSeek) | `/ask-lean` |
| QA colaborativo | `/collab-qa` |
| Benchmarks estrictos | `/benchmark-qa` |
| Theorem proving workflow | `/lean4-theorem-proving` |

## Continuidad de Sesión

**REGLA**: Al iniciar sesión, ANTES de hacer cualquier cosa:
1. Leer este `CLAUDE.md` y el roadmap/session notes más reciente
2. Identificar la fase/subfase actual y las tareas pendientes
3. **CONTINUAR desde donde se quedó** — NO re-planificar con /plan-project
4. Solo invocar `/plan-project` si el usuario lo pide explícitamente o si hay una tarea NUEVA sin plan

**NO re-planificar trabajo existente.** Si el usuario dice "continuemos", leer el plan y ejecutar el siguiente paso pendiente.

## Protocolo de Ejecución

### Scout Phase (OBLIGATORIO antes de cada bloque de trabajo)
```bash
python3 ~/.claude/skills/plan-project/scripts/scout.py \
  --targets "{nodos_a_trabajar}" --context-lines 5 {archivos}
```
Genera Code Map (~2-3K tok, 0 LLM). Trabajar con el Code Map, NO leer archivos completos.

### Modo de ejecución por tipo de nodo
- **Hojas**: Agent Teams en paralelo si ≥2 nodos independientes
- **Intermedios**: Agent Teams si ≥3, secuencial si menos
- **Fundacionales/Críticos**: SIEMPRE secuencial, con firewall `_aux`

### Escalación (hooks lo enforzan)
- Intentos 1-2: directo | 3: /ask-dojo | 4: /ask-lean | persiste: reformular

### Checkpoints (hook H enforza cada 3 edits)
- HOJA → `lake env lean {archivo}` | FUNDACIONAL → `lake build` completo

## Patrones Técnicos Probados (de VR1CS-Lean)

### Recursión con Fuel
Toda función recursiva sobre el e-graph usa `fuel : Nat` explícito.
Teoremas separados prueban que `fuel = parent.size` (o análogo) siempre alcanza.
NUNCA usar well-founded recursion sobre estado mutable.

### Firewall `_aux`
Para teoremas fundacionales/críticos:
1. Crear `theorem nombre_aux` con signatura flexible
2. Probar `_aux` sin tocar el teorema original
3. Migrar solo cuando `_aux` compile sin sorry
4. `lake build` completo después

### Arrays Funcionales
Usar `Array.set` de Lean 4. Más lento que imperativo pero verificable.
Suficiente para e-graphs de optimización (no SMT-scale).

### foldl con tipos explícitos
Lean 4.26 requiere tipos explícitos en lambdas de `foldl`:
```lean
-- CORRECTO:
list.foldl (fun acc (x : MiTipo) => acc + x.size) 0
-- INCORRECTO (falla type inference):
list.foldl (fun acc x => acc + x.size) 0
```

### Doc comments y #eval
Los doc comments (`/-- ... -/`) solo van antes de `def`, `theorem`, `lemma`, `structure`.
NUNCA antes de `#eval` — usar comentarios regulares (`-- ...`).

## Referencia VR1CS-Lean

Archivos fuente de referencia (para consulta, NO modificar):

| Archivo VR1CS | LOC | Thms | Acoplamiento R1CS |
|--------------|:---:|:----:|:-----------------:|
| `EGraph/UnionFind.lean` | 1,235 | 44 | CERO (copia directa) |
| `EGraph/Core.lean` | ~800 | — | `CircuitNodeOp` hardcoded → generalizar |
| `EGraph/CoreSpec.lean` | 1,368 | 64 | Indirecto via `ENode` → genérico |
| `EGraph/SemanticSpec.lean` | 2,061 | 36 | `ZMod p` profundo → `Val` genérico |
| `EGraph/EMatch.lean` | ~400 | — | `CircuitPattern` → `Pattern Op` |
| `EGraph/Saturate.lean` | ~200 | — | Solo via `RewriteRule` → genérico |
| `EGraph/Optimize.lean` | ~300 | — | Mixto → separar genérico/dominio |
| `EGraph/ILP.lean` | ~180 | — | Solo via `ENode` → genérico |
| `EGraph/ILPEncode.lean` | ~250 | — | Solo via `CostModel` → genérico |
| `EGraph/ILPSolver.lean` | ~300 | — | CERO |
| `EGraph/ILPCheck.lean` | ~200 | 1 | Via `extractILP` → genérico |
| `EGraph/ILPSpec.lean` | ~180 | 3 | `ZMod p` → `Val` genérico |
| `EGraph/ParallelMatch.lean` | ~175 | — | Solo via `RewriteRule` → genérico |
| `EGraph/ParallelSaturate.lean` | ~150 | — | Solo via `RewriteRule` → genérico |
