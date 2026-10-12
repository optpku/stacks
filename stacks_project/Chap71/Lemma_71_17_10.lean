/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Definition_71_17_1_Blowup
public import stacks_project.Chap71.Definition_71_6_6_Sum
public import stacks_project.Chap71.Lemma_71_18_7_Blowup

/-!
# Composition of successive blowups in a product of ideal sheaves

A blowup in a quasi-coherent ideal, followed by a blowup in the inverse image
of a second quasi-coherent ideal, is a blowup in the product ideal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/-- Lemma 71.17.10: let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `I ⊂ 𝒪_X` and `J` be quasi-coherent sheaves of ideals. Let `π : Blowup X I`
be the blowing up of `X` in `I`. Let `π' : Blowup π.space (J.pullback π.hom)`
be the blowing up of `π.space` in the inverse-image ideal `J.pullback π.hom`.
Then the composite `π'.hom ≫ π.hom` is a blowup of `X` in the product ideal
`IdealSubobject.mul I J`. -/
@[stacks 085Y]
theorem compIsBlowup {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I J : IdealSubobject X) [IsQuasiCoherent I] [IsQuasiCoherent J]
    (π : Blowup X I) (π' : Blowup π.space (J.pullback π.hom)) :
    IsBlowup (π'.hom ≫ π.hom) (center (IdealSubobject.mul I J)) :=
  sorry

/-- The composite of a blowup in `I` with a blowup in the inverse image of `J`
carries its canonical blowup structure in the product ideal. -/
instance instIsBlowup_comp {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I J : IdealSubobject X) [IsQuasiCoherent I] [IsQuasiCoherent J]
    (π : Blowup X I) (π' : Blowup π.space (J.pullback π.hom)) :
    IsBlowup (π'.hom ≫ π.hom) (center (IdealSubobject.mul I J)) :=
  sorry

/-- The composite of successive blowups in `I` and in the inverse image of `J`
is isomorphic over `X` to a chosen blowup of `X` in `IdealSubobject.mul I J`. -/
theorem isoOver_comp {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I J : IdealSubobject X) [IsQuasiCoherent I] [IsQuasiCoherent J]
    (π : Blowup X I) (π' : Blowup π.space (J.pullback π.hom))
    (ρ : Blowup X (IdealSubobject.mul I J)) :
    Nonempty (Over.mk (π'.hom ≫ π.hom) ≅ Over.mk ρ.hom) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
