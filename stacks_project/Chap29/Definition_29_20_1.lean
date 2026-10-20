module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Definition 29.20.1 (1): a morphism is quasi-finite at a source point exactly when compatible
affine neighborhoods induce a finite-type ring map that is quasi-finite at the corresponding
prime. -/
@[stacks 01TD] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt.iff_exists_affineNeighborhood :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (x : X),
      AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt f x ↔
        ∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens),
          ∃ V : S.affineOpens, ∃ e : U ≤ f ⁻¹ᵁ V,
            (CommRingCat.Hom.hom (f.appLE V U e)).FiniteType ∧
              (CommRingCat.Hom.hom (f.appLE V U e)).QuasiFiniteAt
                (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal)

/- Definition 29.20.1 (2): local quasi-finiteness in the finite-type sense holds exactly when
the finite-type point predicate holds at every source point. -/
@[stacks 01TD] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.locallyQuasiFinite_iff_forall_quasiFiniteAt :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.LocallyOfFiniteType f ∧ AlgebraicGeometry.LocallyQuasiFinite f ↔
        ∀ x : X, AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt f x)

/- Definition 29.20.1 (3): a morphism is quasi-finite exactly when it is of finite type and every
source point is isolated in its fibre. -/
@[stacks 01TD] #check
  (AlgebraicGeometry.Scheme.Hom.quasiFinite_iff_finiteType_and_isOpen_singleton_asFiber :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.Scheme.Hom.QuasiFinite f ↔
        AlgebraicGeometry.Scheme.Hom.FiniteType f ∧
          ∀ x : X, IsOpen ({f.asFiber x} : Set (f.fiber (f x))))
