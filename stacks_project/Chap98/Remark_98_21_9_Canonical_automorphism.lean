module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.CanonicalAutomorphism
public import stacks_project.Chap98.Remark_98_21_9_Canonical_automorphism_Kaehler
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.GroupoidsOver

universe u

/- Remark 98.21.9 (Canonical automorphism)
For a fibre morphism over Spec(B) between objects descending from Spec(A),
the difference of its pullbacks along b ↦ (b, d b) and b ↦ (b, 0) is an
infinitesimal automorphism with values in the Kähler differential module.
-/
@[stacks 07YD] #check (AlgebraicGeometry.GroupoidsOver.canonicalAut :
  {S : Scheme.{u}} → {X : GroupoidsOver S} →
    {A B : CommRingCat.{u}} → {σA : Spec A ⟶ S} → (v : A ⟶ B) →
    (x y : X.p.Fiber (Over.mk σA)) →
    [HasStrongRimSchlessinger X] → [IsLocallyNoetherian S] →
    σA.MapsIntoAffineOpen →
    (Chosen.reindexObj X.p (specOverHom v rfl) x ⟶
      Chosen.reindexObj X.p (specOverHom v rfl) y) →
    (infFunctor (Chosen.reindexObj X.p (specOverHom v rfl) x)).obj
      (CommRingCat.KaehlerDifferential v))
