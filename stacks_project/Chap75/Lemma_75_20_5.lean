module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange.InternalHom.TorIndependence
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Hom
open CategoryTheory.Limits CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure CategoryTheory.DerivedCategory

universe u

/- Lemma 75.20.5 (1): for a Tor-independent cartesian square of qcqs algebraic spaces
over `g : Spec B ⟶ Spec A`, the canonical derived internal-Hom base-change map
`RHom_X(M, K) ⊗^L_A B ⟶ RHom_{X'}(L(g')^* M, L(g')^* K)` in `D(B)` is an isomorphism
when `M` is perfect and `K` lies in `D_QCoh(X)`. -/
@[stacks 0E4S] #check
  (AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.InternalHom.map_isIso_of_isPerfect :
    ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B) {X X' : AlgebraicSpace (Spec A)}
      (g' : X' ⟶ X) (f' : X' ⟶ ofOver (Over.mk (Spec.map φ)))
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec A))))
      [IsQuasiCompact X] [IsQuasiSeparated X]
      [IsQuasiCompact X'] [IsQuasiSeparated X']
      [QuasiCompact f] [QuasiSeparated f]
      [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
      [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
      (sq : IsPullback g' f' f (specMap φ)),
      TorIndependentOver (Over.mk f) (Over.mk (specMap φ)) →
        ∀ (H_X : MonoidalClosed (ModuleDerived X))
          (H_X' : MonoidalClosed (ModuleDerived X'))
          (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
          (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
          (M : ModuleDerived X) (K : DerivedQCoh X),
          ModuleDerived.IsPerfect M →
            IsIso (DerivedBaseChange.InternalHom.canonicalMap sq.toCommSq H_X H_X' T_X T_X' M K.obj))

/- Lemma 75.20.5 (2): for a Tor-independent cartesian square of qcqs algebraic spaces
over `g : Spec B ⟶ Spec A`, the same canonical map in `D(B)` is an isomorphism when
`M` is pseudo-coherent, `K` lies in `D_QCoh^+(X)`, and `B` has finite Tor dimension
over `A`. -/
@[stacks 0E4S] #check
  (AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.InternalHom.map_isIso_of_isPseudoCoherent :
    ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B) {X X' : AlgebraicSpace (Spec A)}
      (g' : X' ⟶ X) (f' : X' ⟶ ofOver (Over.mk (Spec.map φ)))
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec A))))
      [IsQuasiCompact X] [IsQuasiSeparated X]
      [IsQuasiCompact X'] [IsQuasiSeparated X']
      [QuasiCompact f] [QuasiSeparated f]
      [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
      [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
      (sq : IsPullback g' f' f (specMap φ)),
      TorIndependentOver (Over.mk f) (Over.mk (specMap φ)) →
        ∀ (H_X : MonoidalClosed (ModuleDerived X))
          (H_X' : MonoidalClosed (ModuleDerived X'))
          (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
          (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
          (M : ModuleDerived X) (K : DerivedQCoh X),
          IsPseudoCoherent X M →
            (t.plus : ObjectProperty (ModuleDerived X)) K.obj →
              φ.hom.HasFiniteTorDimension →
                IsIso (DerivedBaseChange.InternalHom.canonicalMap sq.toCommSq H_X H_X' T_X T_X' M K.obj))
