/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian
public import ReasLib.Topology.Sheaves.Spectral.GlobalSections

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a proper morphism over a henselian pair, restriction of any sheaf to the special-fibre
pullback induces a bijection on global sections. -/
theorem globalSectionsBijectiveOfProperHenselianPair
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.toTopCat.Sheaf (Type u)) :
    Function.Bijective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
        (pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).base).unit.app F).hom.app
            (op (⊤ : TopologicalSpace.Opens X.toTopCat))) := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
