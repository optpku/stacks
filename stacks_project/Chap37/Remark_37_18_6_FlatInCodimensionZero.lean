/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.CodimensionZero

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Flatness of a scheme module over the base at every generic point of every fibre. -/
#check
  (AlgebraicGeometry.Scheme.Modules.flatOverInCodimensionZero :
    ∀ {X S : Scheme.{u}}, X.Modules → (X ⟶ S) → Prop)

/- Codimension-zero flatness gives flatness at a generic point of a chosen fibre. -/
#check
  (AlgebraicGeometry.Scheme.Modules.flatOverInCodimensionZero.flatOverAt :
    ∀ {X S : Scheme.{u}} {ℱ : X.Modules} {f : X ⟶ S}
      (h : flatOverInCodimensionZero ℱ f) (s : S) (x : f.fiber s)
      (hx : x ∈ genericPoints (f.fiber s)),
      Scheme.Modules.flatOverAt ℱ f ((f.fiberι s) x))

/- Flatness over the base implies flatness over the base in codimension zero. -/
#check
  (AlgebraicGeometry.Scheme.Modules.flatOverInCodimensionZero.of_flatOver :
    ∀ {X S : Scheme.{u}} {ℱ : X.Modules} {f : X ⟶ S},
      Scheme.Modules.flatOver ℱ f → flatOverInCodimensionZero ℱ f)

end AlgebraicGeometry.Scheme.Modules
