/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Adjunction.InternalHom
public import ReasLib.CategoryTheory.Monoidal.Functor.TensorComparison
public import stacks_project.Chap75.Lemma_75_20_5_InternalHom

/-!
# Derived internal Hom, multiplication, and the pullback-pushforward counit

A commutative square of algebraic spaces induces canonical identifications of
iterated derived pushforwards and a global internal-Hom adjunction isomorphism.
Together with the counit `L(g')^* R(g')_* L ⟶ L`, these supply the remaining three
edges of the internal-Hom base-change square.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Hom
open CategoryTheory.Limits CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The canonical identification of the composite derived pushforward with derived
pushforward along a composite morphism, obtained from uniqueness of right adjoints
after transporting the composite adjunction along the derived-pullback composition
comparison. -/
noncomputable def pushforwardDerived.compIso {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIso (modulePullbackDerived.compComparison f g)] :
    pushforwardDerived f ⋙ pushforwardDerived g ≅ pushforwardDerived (f ≫ g) :=
  (((modulePullbackDerivedPushforwardAdjunction g).comp
      (modulePullbackDerivedPushforwardAdjunction f)).ofNatIsoLeft
        (asIso (modulePullbackDerived.compComparison f g))).rightAdjointUniq
    (modulePullbackDerivedPushforwardAdjunction (f ≫ g))

/-- The derived-pushforward composition isomorphism is the uniqueness isomorphism
between the transported composite adjunction and derived pushforward along the
composite morphism. -/
theorem pushforwardDerived.compIso_eq {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIso (modulePullbackDerived.compComparison f g)] :
    pushforwardDerived.compIso f g =
      (((modulePullbackDerivedPushforwardAdjunction g).comp
          (modulePullbackDerivedPushforwardAdjunction f)).ofNatIsoLeft
            (asIso (modulePullbackDerived.compComparison f g))).rightAdjointUniq
        (modulePullbackDerivedPushforwardAdjunction (f ≫ g)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange.InternalHom

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
variable (g' : X' ⟶ X) {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
variable [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
variable [(modulePullbackDerived g').Monoidal]
variable [IsIso (modulePullbackDerived.compComparison f' g)]
variable [IsIso (modulePullbackDerived.compComparison g' f)]

/-- The canonical identification of the two iterated derived pushforwards associated to a
commutative square of algebraic spaces. -/
noncomputable def pushforwardIso (sq : CommSq g' f' f g) :
    Modules.pushforwardDerived g' ⋙ Modules.pushforwardDerived f ≅
      Modules.pushforwardDerived f' ⋙ Modules.pushforwardDerived g :=
  Modules.pushforwardDerived.compIso g' f ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y ↦ Modules.pushforwardDerived h) sq.w) ≪≫
    (Modules.pushforwardDerived.compIso f' g).symm

/-- The forward component of `pushforwardIso` is the two composition isomorphisms with the
commutative-square transport between them. -/
theorem pushforwardIso_hom_app (sq : CommSq g' f' f g)
    (K : ModuleDerived X') :
    (pushforwardIso g' sq).hom.app K =
      (Modules.pushforwardDerived.compIso g' f).hom.app K ≫
        eqToHom (congrArg
          (fun h : X' ⟶ Y ↦ (Modules.pushforwardDerived h).obj K) sq.w) ≫
        (Modules.pushforwardDerived.compIso f' g).inv.app K :=
  sorry

/-- The global internal-Hom adjunction isomorphism, transported across the two canonical
derived-pushforward composition isomorphisms of a commutative algebraic-space square. -/
noncomputable def globalHomAdjunctionIso (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (M : ModuleDerived X) (L : ModuleDerived X') :
    (Modules.pushforwardDerived f).obj
        ((H_X.ihomOf M).obj ((Modules.pushforwardDerived g').obj L)) ≅
      (Modules.pushforwardDerived g).obj
        ((Modules.pushforwardDerived f').obj
          ((H_X'.ihomOf ((modulePullbackDerived g').obj M)).obj L)) :=
  (Modules.pushforwardDerived f).mapIso
      (CategoryTheory.Adjunction.InternalHom.comparisonIso
        (modulePullbackDerivedPushforwardAdjunction g') H_X H_X'
        (Functor.TensorComparison.ofMonoidal (modulePullbackDerived g')) M L) ≪≫
    (pushforwardIso g' sq).app
      ((H_X'.ihomOf ((modulePullbackDerived g').obj M)).obj L)

/-- The forward map of `globalHomAdjunctionIso` is pushforward of the internal-Hom
comparison followed by the pushforward-composition transport. -/
theorem globalHomAdjunctionIso_hom (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (M : ModuleDerived X) (L : ModuleDerived X') :
    (globalHomAdjunctionIso g' sq H_X H_X' M L).hom =
      (Modules.pushforwardDerived f).map
          (CategoryTheory.Adjunction.InternalHom.comparisonIso
            (modulePullbackDerivedPushforwardAdjunction g') H_X H_X'
            (Functor.TensorComparison.ofMonoidal (modulePullbackDerived g'))
            M L).hom ≫
        (pushforwardIso g' sq).hom.app
          ((H_X'.ihomOf ((modulePullbackDerived g').obj M)).obj L) :=
  sorry

/-- The right edge obtained by applying internal Hom to the counit
`L(g')^* R(g')_* L ⟶ L` and then applying derived pushforward along `f'`. -/
noncomputable def adjunctionCounitMap (f' : X' ⟶ Y')
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (M : ModuleDerived X) (L : ModuleDerived X') :
    (Modules.pushforwardDerived f').obj
        ((H_X'.ihomOf ((modulePullbackDerived g').obj M)).obj
          ((modulePullbackDerived g').obj
            ((Modules.pushforwardDerived g').obj L))) ⟶
      (Modules.pushforwardDerived f').obj
        ((H_X'.ihomOf ((modulePullbackDerived g').obj M)).obj L) :=
  (Modules.pushforwardDerived f').map
    ((H_X'.ihomOf ((modulePullbackDerived g').obj M)).map
      ((modulePullbackDerivedPushforwardAdjunction g').counit.app L))

/-- The counit edge is derived pushforward of internal Hom applied to the
pullback-pushforward counit. -/
theorem adjunctionCounitMap_spec (f' : X' ⟶ Y')
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (M : ModuleDerived X) (L : ModuleDerived X') :
    adjunctionCounitMap g' f' H_X' M L =
      (Modules.pushforwardDerived f').map
        ((H_X'.ihomOf ((modulePullbackDerived g').obj M)).map
          ((modulePullbackDerivedPushforwardAdjunction g').counit.app L)) :=
  sorry

/-- Multiplication on global derived Hom first uses the global internal-Hom adjunction
isomorphism and then applies the counit `L(g)^* R(g)_* K' ⟶ K'`. -/
noncomputable def multiplication (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (M : ModuleDerived X) (L : ModuleDerived X') :
    (source f g).obj
        ((H_X.ihomOf M).obj ((Modules.pushforwardDerived g').obj L)) ⟶
      (Modules.pushforwardDerived f').obj
        ((H_X'.ihomOf ((modulePullbackDerived g').obj M)).obj L) :=
  (modulePullbackDerived g).map (globalHomAdjunctionIso g' sq H_X H_X' M L).hom ≫
    (modulePullbackDerivedPushforwardAdjunction g).counit.app _

/-- Multiplication factors through pullback of the global internal-Hom adjunction isomorphism
and ends in the canonical derived pullback-pushforward counit. -/
theorem multiplication_spec (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (M : ModuleDerived X) (L : ModuleDerived X') :
    multiplication g' sq H_X H_X' M L =
      (modulePullbackDerived g).map
          (globalHomAdjunctionIso g' sq H_X H_X' M L).hom ≫
        (modulePullbackDerivedPushforwardAdjunction g).counit.app _ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange.InternalHom

namespace AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.InternalHom

/-- For an affine Tor-independent cartesian square of qcqs algebraic spaces, the derived
internal-Hom base-change map commutes with multiplication and the morphism induced by the
pullback-pushforward counit. -/
theorem map_counit_commSq {A B : CommRingCat.{u}} (φ : A ⟶ B)
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
    (M : ModuleDerived X) (L : ModuleDerived X') :
    CommSq
      (Hom.DerivedBaseChange.InternalHom.map sq.toCommSq H_X H_X' M
        ((Modules.pushforwardDerived g').obj L))
      (Hom.DerivedBaseChange.InternalHom.multiplication g' sq.toCommSq H_X H_X' M L)
      (Hom.DerivedBaseChange.InternalHom.adjunctionCounitMap g' f' H_X' M L)
      (𝟙 _) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.InternalHom
