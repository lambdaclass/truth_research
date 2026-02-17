# Lecciones Aprendidas: LambdaSat-Lean Fases 3 + 4

## L-301: unfold + simp only [] + split — patron para funciones recursivas con let

**Contexto**: `extractF` y `extractILP` son funciones recursivas con multiples `let` bindings y `match` anidados. `split at hext` falla directamente porque no puede operar sobre `let`/`have` bindings.

**Solucion**: El patron de tres pasos:
```lean
unfold extractF at hext
simp only [] at hext  -- zeta-reduce let bindings
split at hext         -- now match expressions are exposed
```

`simp only []` sin argumentos realiza zeta-reduccion (elimina `let` bindings) sin reescribir nada mas. Esto expone los `match` para que `split` pueda actuar.

**Aplicabilidad**: Cualquier prueba por induccion sobre funciones con `let` intermedios en Lean 4.

---

## L-302: ValidSolution innecesaria para correctness de ILP extraction

**Contexto**: El plan asumia que `ValidSolution` (checkSolution passes) era necesaria para probar `extractILP_correct`. Esto requeria `validSol_selected_in_class`, un teorema sobre `HashMap.fold` que era muy dificil de probar.

**Descubrimiento**: Si `extractILP g sol classId fuel = some expr`, todos los matches intermedios (`selectedNodes.get?`, `classes.get?`, bounds check, `mapOption`) ya fueron exitosos. La hipotesis `ValidSolution` es redundante — la hipotesis de extraccion exitosa (`hext : extractILP ... = some expr`) ya implica todo lo necesario.

**Leccion**: Antes de probar un lemma auxiliar dificil, verificar si la hipotesis principal (exito de la funcion) ya contiene la informacion necesaria via pattern matching exitoso. `split at hext` destruye cada caso, y los casos `none` se descartan con `absurd hext (by simp)`.

**Ahorro**: Elimino la necesidad de `validSol_selected_in_class` (HashMap.fold reasoning) y simplifico la prueba en ~50 LOC.

---

## L-303: Double consistent_root_eq' para ILP vs single para greedy

**Contexto**: `extractF` llama recursivamente con `extractF g c fuel` (child directo). `extractILP` llama con `extractILP g sol (root uf c) fuel` (child canonicalizado).

**Consecuencia**: En la prueba de `extractILP_correct`, el IH da `v (root uf (root uf c))` pero el goal necesita `v c`. Esto requiere **dos** aplicaciones de `consistent_root_eq'`:
```lean
rw [consistent_root_eq' g env v hcv hwf _]  -- root(root(c)) → root(c)
exact consistent_root_eq' g env v hcv hwf _  -- root(c) → c
```

En `extractF_correct` solo se necesita una.

**Leccion**: Funciones que pre-canonizan argumentos recursivos generan obligaciones de prueba con composicion de root. Anticipar cuantas capas de `root` hay en las llamadas recursivas.

---

## L-304: DecidableEq via deriving es superior a BEq manual

**Contexto**: Primer intento de `BEq ArithOp` con match manual fallo en `LawfulBEq` porque:
- `eq_of_beq` requiere probar `a = b` desde `beq a b = true`
- Los subcases con `obtain ⟨h1, h2⟩ := h` no cerraban bien
- `LawfulHashable` fallaba con `subst h` porque `h : (a == b) = true` no es `a = b`

**Solucion**: `deriving DecidableEq` + `beq a b := decide (a = b)`:
```lean
inductive ArithOp where ... deriving DecidableEq
instance : BEq ArithOp where beq a b := decide (a = b)
instance : LawfulBEq ArithOp where
  eq_of_beq h := by simp [BEq.beq] at h; exact h
  rfl := by simp [BEq.beq]
```

`simp [BEq.beq]` automaticamente convierte `decide (a = b) = true` a `a = b`.

**Leccion**: Para tipos inductivos concretos, siempre usar `DecidableEq` como base para `BEq`/`LawfulBEq`. Evita match-explosion manual.

---

## L-305: EvalExpr recursivo no puede definirse inline en instance

**Contexto**: Definir `evalExpr` directamente en la instancia con llamadas recursivas a `EvalExpr.evalExpr`:
```lean
instance : EvalExpr ArithExpr Nat where
  evalExpr
    | .add l r, env => EvalExpr.evalExpr l env + EvalExpr.evalExpr r env
    ...
```
Falla con "failed to synthesize EvalExpr ArithExpr Nat" — referencia circular durante definicion.

**Solucion**: Definir la funcion recursiva por separado, luego usarla en la instancia:
```lean
def evalArithExpr : ArithExpr → (Nat → Nat) → Nat
  | .add l r, env => evalArithExpr l env + evalArithExpr r env
  ...
instance : EvalExpr ArithExpr Nat where evalExpr := evalArithExpr
```

**Leccion**: Lean 4 no permite referirse a un typeclass instance durante su propia definicion. Funciones recursivas de typeclass siempre deben definirse como `def` standalone primero.

---

## L-306: Generalizacion typeclass reduce LOC pero no necesariamente teoremas

**Contexto**: El plan estimaba ~32 teoremas nuevos para F3+F4. La realidad fueron 18. La generalizacion con typeclasses permitio:
- Probar `extractF_correct` directamente sin lemmas auxiliares separados
- Eliminar `validSol_selected_in_class` completamente
- Unificar patrones de prueba entre greedy e ILP

**Estadistica**: VR1CS tiene 158 teoremas para e-graph, LambdaSat tiene 181 en total pero solo 18 nuevos en F3+F4. La generalizacion typeclass absorbe complejidad en las leyes del typeclass (`reconstruct_sound`, `evalOp_ext`, `evalOp_mapChildren`) en vez de lemmas separados.

**Leccion**: El conteo de teoremas no es una buena metrica de complejidad. Un typeclass bien disenado con leyes expresivas puede reducir el numero de lemmas auxiliares drasticamente.

---

## L-307: Copia directa de modulos zero-coupling funciona perfectamente

**Contexto**: Los modulos ILP.lean, ILPEncode.lean, ILPSolver.lean tienen ZERO acoplamiento con CircuitNodeOp/CircuitExpr/ZMod en VR1CS. Se copiaron con solo cambio de namespace.

**Resultado**: 726 LOC copiados, 0 modificaciones sustantivas, compilacion exitosa al primer intento.

**Leccion**: El analisis de acoplamiento previo (grep por tipos concretos) es un predictor perfecto de esfuerzo de portabilidad. Para futuros proyectos de generalizacion:
1. Grep todos los tipos concretos del dominio en cada archivo
2. Archivos con ZERO matches = copia directa
3. Archivos con matches = requieren typeclass adaptation

---

## L-308: NodeSemantics.evalOp_mapChildren habilita congruencia gratis

**Contexto**: La ley `evalOp_mapChildren` del typeclass `NodeSemantics`:
```lean
evalOp (mapChildren f op) env v = evalOp op env (fun c => v (f c))
```
Permite probar que canonicalizar children (via `mapChildren (root uf)`) no cambia la semantica — solo precompone la valuacion con `root`.

**Leccion**: Incluir leyes de "comutacion con mapChildren" en typeclasses semanticos es crucial para e-graphs, donde canonicalizacion de children es ubicua.

---

## L-309: ExtractableSound como Prop standalone > como ley de typeclass

**Contexto**: El diseno inicial ponia `reconstruct_sound` como ley dentro del typeclass `Extractable`. El diseno final usa:
```lean
def ExtractableSound (Op Expr Val : Type) [...] : Prop := ...
```
Como una proposicion standalone, pasada como hipotesis explicita a los teoremas.

**Ventajas**:
- Evita phantom type `Val` en `Extractable` (solo necesita `Op` y `Expr`)
- Permite instanciar `Extractable` sin probar soundness inmediatamente
- Los tests operacionales no necesitan `Val` ni `NodeSemantics`
- Soundness se conecta solo cuando se hacen pruebas formales

**Leccion**: Separar operational interfaces (typeclasses) de verification obligations (Props/hypotheses). No todo tiene que ser una ley de typeclass.

---

## L-310: mapOption con spec lemmas es mejor que List.mapM/traverse

**Contexto**: `extractF` necesita extraer todos los children y fallar si alguno falla. Opciones:
1. `List.mapM` con `Option` monad — dificil de razonar
2. `mapOption` custom con lemmas de spec

**Resultado**: `mapOption` con 4 lemmas (nil, cons_inv, length, get) permitio cerrar las pruebas de `extractF_correct` y `extractILP_correct` sin dificultad. El lemma `mapOption_get` es especialmente util:
```lean
mapOption f l = some results → f l[i] = some results[i]
```

**Leccion**: Para verificacion formal, preferir helpers custom con spec lemmas sobre stdlib combinators. El costo de los 4 lemmas (~40 LOC) se amortiza en multiples pruebas.

---

## L-311: Array.getElem_mem_toList para membership desde indexacion

**Contexto**: En `extractILP_correct`, el nodo seleccionado es `eclass.nodes[nodeIdx]` (acceso por indice). Pero `ConsistentValuation` requiere `node ∈ eclass.nodes.toList` (membership en lista).

**Puente**:
```lean
have hnode_mem : (eclass.nodes[nodeIdx]) ∈ eclass.nodes.toList :=
  Array.getElem_mem_toList hidx
```

Donde `hidx : nodeIdx < eclass.nodes.size`.

**Leccion**: `Array.getElem_mem_toList` es el puente estandar entre array indexing y list membership en Lean 4. Util en cualquier prueba que mezcle arrays (operacional) con listas (especificacion).

---

## L-312: Parallel saturation threshold evita overhead en grafos pequenos

**Contexto**: `parallelSaturate` con `parallelThreshold := 1` funciona pero agrega overhead de IO/Tasks para grafos de 3 clases. El threshold default de 20 clases cae automaticamente a sequential.

**Leccion**: Siempre incluir threshold adaptativo en wrappers paralelos. En tests, usar threshold bajo para ejercitar el path paralelo.

---

## Resumen

| ID | Titulo corto | Impacto |
|----|-------------|---------|
| L-301 | unfold+simp only[]+split | CRITICO — patron universal |
| L-302 | ValidSolution innecesaria | ALTO — elimino sorry dificil |
| L-303 | Double root bridge | MEDIO — patron predecible |
| L-304 | DecidableEq para BEq | MEDIO — evita match-explosion |
| L-305 | Recursive instance circular | MEDIO — pattern comun |
| L-306 | Typeclasses reducen lemmas | MEDIO — metrica vs realidad |
| L-307 | Zero-coupling = copia directa | ALTO — prediccion de esfuerzo |
| L-308 | evalOp_mapChildren | MEDIO — diseno de typeclass |
| L-309 | ExtractableSound standalone | ALTO — diseno arquitectural |
| L-310 | mapOption con spec lemmas | ALTO — patron de verificacion |
| L-311 | Array.getElem_mem_toList | BAJO — puente util |
| L-312 | Parallel threshold | BAJO — engineering |

---

*Generado: 2026-02-17*
*Proyecto: LambdaSat-Lean v0.1.0*
*Fases: F3 (Extraction) + F4 (ILP + Parallel + TranslationValidation)*
