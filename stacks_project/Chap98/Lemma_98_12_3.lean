module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt.Completion
import StacksCheckRecall

/-! # Versality at a finite type point and its completed-stalk formal object -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing
open AlgebraicGeometry.GroupoidsOver
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 98.12.3: an object is versal at a finite type point if and only if
its associated formal object over the completed stalk is versal. -/
@[stacks 0CXK] #check (AlgebraicGeometry.GroupoidsOver.isVersalAt_iff_isVersal :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0],
    IsVersalAt hU x hx u0 ↔
      ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
        [Algebra Λ (associatedFormalObject hU x hx u0).base.carrier]
        [Module.Finite Λ
          (ResidueField (associatedFormalObject hU x hx u0).base.carrier)]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion]
        (h_toS :
          Spec.map (CommRingCat.ofHom
                (algebraMap Λ
                  (associatedFormalObject hU x hx u0).base.carrier)) ≫
              openImmersion =
            (associatedFormalObject hU x hx u0).base.toS),
        _root_.FormalObject.IsVersal
          (FormalObject.toPredeformation
            (associatedFormalObject hU x hx u0) openImmersion h_toS))
