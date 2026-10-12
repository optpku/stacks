/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison
public import ReasLib.RingTheory.RingHom.TorDimension
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_20_4_BaseChange

/-!
# Derived internal Hom and Tor-independent base change on algebraic spaces

A commutative square of algebraic spaces induces a derived internal-Hom base-change
morphism. Over an affine morphism `Spec B ⟶ Spec A`, that morphism is an isomorphism
when the source is perfect, or when the source is pseudo-coherent, the target is
bounded below in `D_QCoh`, and `B` has finite Tor dimension over `A`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Hom
open CategoryTheory.Limits CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The morphism of algebraic spaces over `Spec A` associated to a ring homomorphism
`φ : A ⟶ B`, sending `ofOver (Over.mk (Spec.map φ))` to `ofOver (Over.mk (𝟙 (Spec A)))`. -/
def specMap {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    ofOver (Over.mk (Spec.map φ)) ⟶ ofOver (Over.mk (𝟙 (Spec A))) :=
  ofOverHomMk (Spec.map φ) (Category.comp_id (Spec.map φ))

/-- `specMap φ` is `ofOverHomMk` of `Spec.map φ` over the identity on `Spec A`. -/
theorem specMap_eq {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    specMap φ = ofOverHomMk (Spec.map φ) (Category.comp_id (Spec.map φ)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom

namespace AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange.InternalHom

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
variable [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
variable [(modulePullbackDerived g').Monoidal]
variable [IsIso (modulePullbackDerived.compComparison f' g)]
variable [IsIso (modulePullbackDerived.compComparison g' f)]

/-- The derived internal-Hom base-change morphism associated to a commutative square of
algebraic spaces: apply unbounded derived base change to `ihomOf M K`, then push forward
the pullback/internal-Hom comparison along `L(g')^*`. -/
noncomputable def map (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (M K : ModuleDerived X) :
    (source f g).obj ((H_X.ihomOf M).obj K) ⟶
      (Modules.pushforwardDerived f').obj
        ((H_X'.ihomOf ((modulePullbackDerived g').obj M)).obj
          ((modulePullbackDerived g').obj K)) :=
  (DerivedBaseChange.map sq).app ((H_X.ihomOf M).obj K) ≫
    (Modules.pushforwardDerived f').map
      (Functor.PullbackInternalHom.comparisonOf H_X H_X'
        (modulePullbackDerived g')
        (fun A B ↦ (Functor.Monoidal.μIso (modulePullbackDerived g') A B).symm)
        M K)

/-- The algebraic-space internal-Hom base-change morphism is the derived base-change
component at `ihomOf M K` followed by derived pushforward of the pullback/internal-Hom
comparison. -/
theorem map_spec (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (M K : ModuleDerived X) :
    map sq H_X H_X' M K =
      (DerivedBaseChange.map sq).app ((H_X.ihomOf M).obj K) ≫
        (Modules.pushforwardDerived f').map
          (Functor.PullbackInternalHom.comparisonOf H_X H_X'
            (modulePullbackDerived g')
            (fun A B ↦ (Functor.Monoidal.μIso (modulePullbackDerived g') A B).symm)
            M K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange.InternalHom

namespace AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.InternalHom

/-- In a Tor-independent cartesian square of qcqs algebraic spaces over `Spec B ⟶ Spec A`,
the derived internal-Hom base-change morphism is an isomorphism when the source is perfect
and the target has quasi-coherent cohomology. After identifying `D(O_{S'})` with `D(B)`,
this is the map `RHom_X(M, K) ⊗^L_A B ⟶ RHom_{X'}(L(g')^* M, L(g')^* K)` in `D(B)`. -/
theorem map_isIso_of_isPerfect {A B : CommRingCat.{u}} (φ : A ⟶ B)
    {X X' : AlgebraicSpace (Spec A)} (g' : X' ⟶ X)
    (f' : X' ⟶ ofOver (Over.mk (Spec.map φ)))
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec A))))
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [IsQuasiCompact X'] [IsQuasiSeparated X']
    [QuasiCompact f] [QuasiSeparated f]
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
    [(modulePullbackDerived g').Monoidal]
    [IsIso (modulePullbackDerived.compComparison f' (Hom.specMap φ))]
    [IsIso (modulePullbackDerived.compComparison g' f)]
    (sq : IsPullback g' f' f (Hom.specMap φ))
    (hTor : TorIndependentOver (Over.mk f) (Over.mk (Hom.specMap φ)))
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (M : ModuleDerived X) (K : DerivedQCoh X)
    (hM : ModuleDerived.IsPerfect M) :
    IsIso (Hom.DerivedBaseChange.InternalHom.map sq.toCommSq H_X H_X' M K.obj) :=
  sorry

/-- In a Tor-independent cartesian square of qcqs algebraic spaces over `Spec B ⟶ Spec A`,
the derived internal-Hom base-change morphism is an isomorphism when the source is
pseudo-coherent, the target is bounded below in `D_QCoh`, and `B` has finite Tor dimension
over `A`. After identifying `D(O_{S'})` with `D(B)`, this is the map
`RHom_X(M, K) ⊗^L_A B ⟶ RHom_{X'}(L(g')^* M, L(g')^* K)` in `D(B)`. -/
theorem map_isIso_of_isPseudoCoherent {A B : CommRingCat.{u}} (φ : A ⟶ B)
    {X X' : AlgebraicSpace (Spec A)} (g' : X' ⟶ X)
    (f' : X' ⟶ ofOver (Over.mk (Spec.map φ)))
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec A))))
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [IsQuasiCompact X'] [IsQuasiSeparated X']
    [QuasiCompact f] [QuasiSeparated f]
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
    [(modulePullbackDerived g').Monoidal]
    [IsIso (modulePullbackDerived.compComparison f' (Hom.specMap φ))]
    [IsIso (modulePullbackDerived.compComparison g' f)]
    (sq : IsPullback g' f' f (Hom.specMap φ))
    (hTor : TorIndependentOver (Over.mk f) (Over.mk (Hom.specMap φ)))
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (M : ModuleDerived X) (K : DerivedQCoh X)
    (hM : IsPseudoCoherent X M)
    (hK : (t.plus : ObjectProperty (ModuleDerived X)) K.obj)
    (hφ : φ.hom.HasFiniteTorDimension) :
    IsIso (Hom.DerivedBaseChange.InternalHom.map sq.toCommSq H_X H_X' M K.obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.InternalHom
