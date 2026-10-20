module

import StacksCheckRecall
import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

variable (R : Type u) [CommRing R]
variable (X : AlgebraicSpace (Spec (CommRingCat.of R)))
variable (ℱ 𝒢 : X.Modules) [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (u : ℱ ⟶ 𝒢)
variable (hG_flat : Modules.flatOver 𝒢 (SchemeRealization.toBase X))

/- 0CWA::statement_repair::1 — Situation 77.8.1: `S = Spec (CommRingCat.of R)` is an affine scheme, `X` is an
algebraic space over `S`, `u : ℱ ⟶ 𝒢` is a map of quasi-coherent 𝒪_X-modules, and
`𝒢` is flat over `S`. -/
@[stacks 0CWA] #check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOver :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y), Prop)
#check (Spec (CommRingCat.of R) : Scheme.{u})
#check (inferInstance : IsAffine (Spec (CommRingCat.of R)))
#check (X : AlgebraicSpace (Spec (CommRingCat.of R)))
#check (ℱ : X.Modules)
#check (𝒢 : X.Modules)
#check (inferInstance : ℱ.IsQuasicoherent)
#check (inferInstance : 𝒢.IsQuasicoherent)
#check (u : ℱ ⟶ 𝒢)
#check (SchemeRealization.toBase X : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
#check (hG_flat : Modules.flatOver 𝒢 (SchemeRealization.toBase X))
