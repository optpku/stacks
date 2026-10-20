module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.FinitePresentation

/-!
# Finite-presentation and étale affine-space tests for closed morphisms

The relative affine-space construction and closedness testing predicates are
provided by their mathematical owners. These checks preserve the chapter API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.affineSpaceOver :
  ∀ {S : Scheme.{u}} (V : Over S) (n : ℕ),
    Over S)

#check (AlgebraicGeometry.AlgebraicSpace.affineSpaceOver_left :
  ∀ {S : Scheme.{u}} (V : Over S) (n : ℕ),
    (affineSpaceOver V n).left = 𝔸(ULift.{u} (Fin n); V.left))

#check (AlgebraicGeometry.AlgebraicSpace.affineSpaceOver_hom :
  ∀ {S : Scheme.{u}} (V : Over S) (n : ℕ),
    (affineSpaceOver V n).hom =
      (𝔸(ULift.{u} (Fin n); V.left) ↘ V.left) ≫ V.hom)

namespace affineSpaceOver

#check (AlgebraicGeometry.AlgebraicSpace.affineSpaceOver.proj :
  ∀ {S : Scheme.{u}} (V : Over S) (n : ℕ),
    affineSpaceOver V n ⟶ V)

end affineSpaceOver

namespace affineSpaceOver

#check (AlgebraicGeometry.AlgebraicSpace.affineSpaceOver.proj_left :
  ∀ {S : Scheme.{u}} (V : Over S) (n : ℕ),
    (proj V n).left = (𝔸(ULift.{u} (Fin n); V.left) ↘ V.left))

end affineSpaceOver

namespace Closed

#check (AlgebraicGeometry.AlgebraicSpace.Closed.forallLocallyOfFinitePresentation :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
  Prop)

end Closed

namespace Closed

#check (AlgebraicGeometry.AlgebraicSpace.Closed.forallLocallyOfFinitePresentation_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
  forallLocallyOfFinitePresentation f ↔
      ∀ (Z P : AlgebraicSpace S) (g : Z ⟶ Y) [LocallyOfFinitePresentation g]
        (pZ : P ⟶ Z) (pX : P ⟶ X),
        IsPullback pZ pX g f → Closed pZ)

end Closed

namespace Closed.forallLocallyOfFinitePresentation

#check (AlgebraicGeometry.AlgebraicSpace.Closed.forallLocallyOfFinitePresentation.of :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
  ∀ (h : ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y}
    [LocallyOfFinitePresentation g] {pZ : P ⟶ Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Closed pZ),
    forallLocallyOfFinitePresentation f)

end Closed.forallLocallyOfFinitePresentation

namespace Closed.forallLocallyOfFinitePresentation

#check (AlgebraicGeometry.AlgebraicSpace.Closed.forallLocallyOfFinitePresentation.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
  ∀ (h : forallLocallyOfFinitePresentation f) {Z P : AlgebraicSpace S}
    {g : Z ⟶ Y} [LocallyOfFinitePresentation g] {pZ : P ⟶ Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f),
    Closed pZ)

end Closed.forallLocallyOfFinitePresentation

namespace Closed.forallLocallyOfFinitePresentation

#check (AlgebraicGeometry.AlgebraicSpace.Closed.forallLocallyOfFinitePresentation.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
  ∀ (h : forallLocallyOfFinitePresentation f)
    {Z : AlgebraicSpace S} (g : Z ⟶ Y) [LocallyOfFinitePresentation g]
    [HasPullback f g],
    Closed (pullback.snd f g))

end Closed.forallLocallyOfFinitePresentation

namespace Closed

#check (AlgebraicGeometry.AlgebraicSpace.Closed.existsEtaleAffineSpace :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
  Prop)

end Closed

namespace Closed

#check (AlgebraicGeometry.AlgebraicSpace.Closed.existsEtaleAffineSpace_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
  existsEtaleAffineSpace f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (n : ℕ) (P : AlgebraicSpace S)
          (pA : P ⟶ ofOver (affineSpaceOver V n)) (pX : P ⟶ X),
          IsPullback pA pX (ofOverMap (affineSpaceOver.proj V n) ≫ ψ) f →
            Closed pA)

end Closed

namespace Closed.existsEtaleAffineSpace

#check (AlgebraicGeometry.AlgebraicSpace.Closed.existsEtaleAffineSpace.of :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
  ∀ {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ (n : ℕ) {P : AlgebraicSpace S}
      {pA : P ⟶ ofOver (affineSpaceOver V n)} {pX : P ⟶ X},
      IsPullback pA pX (ofOverMap (affineSpaceOver.proj V n) ≫ ψ) f →
        Closed pA),
    existsEtaleAffineSpace f)

end Closed.existsEtaleAffineSpace

namespace Closed.existsEtaleAffineSpace

#check (AlgebraicGeometry.AlgebraicSpace.Closed.existsEtaleAffineSpace.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
  ∀ (h : existsEtaleAffineSpace f),
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (n : ℕ) {P : AlgebraicSpace S}
          {pA : P ⟶ ofOver (affineSpaceOver V n)} {pX : P ⟶ X},
          IsPullback pA pX (ofOverMap (affineSpaceOver.proj V n) ≫ ψ) f →
            Closed pA)

end Closed.existsEtaleAffineSpace

end AlgebraicGeometry.AlgebraicSpace
