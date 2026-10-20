/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap52.«52_25_1_1_EulerCharacteristic»

@[expose] public section

open scoped AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

namespace CoherentTripleSetup

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The image of `S.f` as a global section of the structure sheaf of
`S.algebraization.X`. -/
def elementOnX (S : CoherentTripleSetup A) : Γ(S.algebraization.X, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).inv S.f

/-- The restriction of `S.f` to an open `V ⊆ S.algebraization.X`. -/
def elementOnXSection (S : CoherentTripleSetup A)
    (V : Opens S.algebraization.X) : Γ(S.algebraization.X, V) :=
  let presheaf := S.algebraization.X.presheaf
  presheaf.map V.leTop.op S.elementOnX

end CoherentTripleSetup

namespace CoherentTriple.Comparison

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {S : CoherentTripleSetup A} {T : CoherentTriple S}

/-- Multiplication by the equation `S.f` is injective on every open of the extension `C.F'`. -/
def MulFInjective (C : T.Comparison) : Prop :=
  ∀ V, Function.Injective (C.F'.smul (S.elementOnXSection V)).hom

end CoherentTriple.Comparison

end AlgebraicGeometry
