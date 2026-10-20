/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.RelativeProj
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Product
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Composition of successive blowups

Blowing up a quasi-coherent ideal and then the inverse image of a second
quasi-coherent ideal gives a blowup in their product, uniquely isomorphic over
the base to any chosen blowup in that product.

Successive blowups of a quasi-compact quasi-separated algebraic space in
finitely presented closed subspaces compose to a blowup in a finitely presented
closed subspace whose underlying point-set is the union of the first center and
the image of the second.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsBlowup

/-- Successive blowups of a quasi-compact, absolutely quasi-separated algebraic
space in finitely presented closed subspaces have composite a blowup in a
finitely presented closed subspace whose underlying point-set is the union of
the first center and the image of the second center. -/
@[stacks 0860]
theorem exists_center_comp {S : Scheme.{u}} {X X' X'' : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (Z : ClosedSubspace X) [FinitePresentation Z.ι]
    (b : X' ⟶ X) [IsBlowup b Z]
    (Z' : ClosedSubspace X') [FinitePresentation Z'.ι]
    (b' : X'' ⟶ X') [IsBlowup b' Z'] :
    ∃ Y : ClosedSubspace X,
      FinitePresentation Y.ι ∧
        Y.pointsSet = Z.pointsSet ∪ Points.map b '' Z'.pointsSet ∧
          IsBlowup (b' ≫ b) Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsBlowup

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/-- Blowing up a quasi-coherent ideal and then the inverse image of a second
quasi-coherent ideal gives a blowup in the product ideal. -/
@[stacks 085Y]
theorem compIsBlowup {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I J : IdealSubobject X) [IsQuasiCoherent I] [IsQuasiCoherent J]
    (π : Blowup X I) (π' : Blowup π.space (J.pullback π.hom)) :
    IsBlowup (π'.hom ≫ π.hom) (center (IdealSubobject.mul I J)) :=
  sorry

/-- Successive blowups in two quasi-coherent ideals admit a unique isomorphism
over the base to any chosen blowup in their product ideal. -/
theorem isoOver_comp {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I J : IdealSubobject X) [IsQuasiCoherent I] [IsQuasiCoherent J]
    (π : Blowup X I) (π' : Blowup π.space (J.pullback π.hom))
    (ρ : Blowup X (IdealSubobject.mul I J)) :
    ∃! e : Over.mk (π'.hom ≫ π.hom) ≅ Over.mk ρ.hom,
      e.hom.left ≫ ρ.hom = π'.hom ≫ π.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
