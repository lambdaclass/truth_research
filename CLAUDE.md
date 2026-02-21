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

## Recurso Adicional

- **VR1CS-Lean (referencia)**: `~/Documents/claudio/vr1cs-lean/VR1CS/EGraph/`

## Protocolo Lean 4

**Continuidad**: Leer CLAUDE.md + ARCHITECTURE.md → identificar fase/nodo actual → CONTINUAR (NO re-planificar). Solo `/plan-project` si el usuario lo pide o tarea NUEVA sin plan. NO crear fases/subfases nuevas sobre plan activo.

**Scout**: `python3 ~/.claude/skills/plan-project/scripts/scout.py --targets "{nodos}" {archivos}` OBLIGATORIO antes de cada bloque. Code Map (~2-3K tok), NO archivos completos.

**Ejecución**: Hojas → paralelo (≥2). Intermedios → paralelo (≥3), secuencial si menos. Fundacionales/Críticos → SIEMPRE secuencial + firewall `_aux`. Gates → de-risk con sketch antes de dependientes.

**Firewall `_aux`**: (1) `theorem nombre_aux` flexible (2) probar sin tocar original (3) migrar cuando compile (4) `lake build` completo.

**Escalación** (hooks enforzan): Directo (1-2) → `solverCascade.py` (3) → `/ask-dojo` (4) → `/ask-lean` (5) → reformular.

**Checkpoints** (hook cada 3 edits): HOJA `lake env lean {f}` | INTERMEDIO + dependientes | FUNDACIONAL `lake build`.

**Verificación post-nodo** (OBLIGATORIA al completar cada nodo del DAG):
1. `verify_node.py --project {path} --files {archivos} --node "{nombre}"` — checks mecánicos (0 LLM tokens)
2. Si mecánicos PASS → QA riguroso via subagente: `collab.py --rounds 1 --detail full` — stress, casos borde, robustez, hipótesis redundantes, calidad de pruebas, coherencia con ARCHITECTURE.md
3. Si QA encuentra problemas → resolver ANTES de continuar. Guardar lección en ARCHITECTURE.md.
4. Registrar resultados en BENCHMARKS.md (sección del nodo, orden topológico).

**Patrones**: Fuel explícito (`Nat`), nunca well-founded sobre mutable. `Array.set` funcional. foldl con tipos explícitos en lambdas. Doc comments solo en `def`/`theorem`/`lemma`/`structure`.

**Recursos**: Bibliografía `~/Documents/claudio/biblioteca/`, Lecciones `~/Documents/claudio/lecciones/lean4/` (usar `query_lessons.py --search/--lesson/--section`), Índices `~/Documents/claudio/biblioteca/indices/`.

**Skills**: `/ask-lean`, `/ask-dojo`, `/lean4-theorem-proving`, `/lean-search`, `/lean-check`, `/lean-goal`, `/lean-diagnostics`. Plugins cameronfreer: proof-search, tactic, error-diagnosis, refactoring, documentation.

**LSP MCP** (lean-lsp): `lean_goal` (proof state at cursor), `lean_diagnostic_messages` (compilation errors), `lean_search` (search Lean environment), `lean_completion` (autocomplete at position). Instant feedback (~30x faster than `lake build` for proof state).

**Subagentes**: Delegar tareas mecánicas (search, análisis, verificación) a Explore subagents. Mantener estrategia de pruebas en conversación principal.

## Hooks (advisory pero de cumplimiento OBLIGATORIO)

Los hooks emiten advertencias o bloqueos. **Seguirlos es obligatorio, sin excepciones:**

| Hook | Trigger | Acción requerida |
|---|---|---|
| `warn-large-read.sh` | Read de source/md >200 líneas sin offset | **BLOQUEADO**. Usar scout.py primero, luego Read con offset+limit |
| `suggest-scout-on-grep.sh` | Grep en directorios source | Considerar scout.py para búsquedas estructurales |
| `edit-guards.sh` | Edit de source o ARCHITECTURE.md | Verificar branch, fan-out Lean, dirty tree, ✓ sin close_block |

**Si un hook emite una advertencia o bloqueo, DETENER y seguir las instrucciones del hook antes de continuar.**

## Rúbrica de benchmarks (durante PLANIFICACIÓN, antes de ejecutar)

Al planificar con `/plan-project`, ANTES de iniciar la ejecución:
1. `/benchmark-qa --strict` → Gemini genera la rúbrica (criterios + targets + metodología)
2. Documentar la rúbrica en `BENCHMARKS.md` sección "Criterios"
3. La rúbrica es el contrato: los bloques se evalúan contra ella al cerrar

**La rúbrica se diseña UNA VEZ al planificar, NO al cerrar. Esto optimiza tokens.**

## Cierre de bloque (OBLIGATORIO)

ANTES de marcar un bloque/nodo como completado:
1. `close_block.py --project . --block "Bloque N" --nodes '{...}'`
2. Ejecutar benchmarks contra la rúbrica ya existente en `BENCHMARKS.md`
3. Si PASS → QA riguroso (`/collab-qa`)
4. Si QA PASS → registrar resultados en `BENCHMARKS.md` → ENTONCES marcar ✓

## Cierre de fase (OBLIGATORIO)

ANTES de cerrar una fase completa:
1. Benchmarks finales comprehensivos contra la rúbrica
2. Registrar lecciones en `ARCHITECTURE.md`
3. Tag de versión

**NUNCA cerrar bloque ni fase sin ejecutar benchmarks contra la rúbrica.**

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
