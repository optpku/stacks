module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.AffineSpectrum
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange.InternalHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
public import ReasLib.RingTheory.RingHom.TorDimension

/-! # Affine Tor-independent internal-Hom base change -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits CategoryTheory.MonoidalClosed CategoryTheory.DerivedCategory
open DerivedCategory.TStructure

universe u

namespace AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.InternalHom

/-- In a Tor-independent cartesian square of qcqs algebraic spaces over `Spec B ⟶ Spec A`,
the derived internal-Hom base-change morphism is an isomorphism when the source is perfect
and the target has quasi-coherent cohomology. Under the affine quasi-coherent identification with `D(B)`,
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
    (sq : IsPullback g' f' f (Hom.specMap φ))
    (hTor : TorIndependentOver (Over.mk f) (Over.mk (Hom.specMap φ)))
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M : ModuleDerived X) (K : DerivedQCoh X)
    (hM : ModuleDerived.IsPerfect M) :
    IsIso (Hom.DerivedBaseChange.InternalHom.canonicalMap sq.toCommSq H_X H_X' T_X T_X' M K.obj) :=
  sorry

/-- In a Tor-independent cartesian square of qcqs algebraic spaces over `Spec B ⟶ Spec A`,
the derived internal-Hom base-change morphism is an isomorphism when the source is
pseudo-coherent, the target is bounded below in `D_QCoh`, and `B` has finite Tor dimension
over `A`. Under the affine quasi-coherent identification with `D(B)`, this is the map
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
    (sq : IsPullback g' f' f (Hom.specMap φ))
    (hTor : TorIndependentOver (Over.mk f) (Over.mk (Hom.specMap φ)))
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M : ModuleDerived X) (K : DerivedQCoh X)
    (hM : IsPseudoCoherent X M)
    (hK : (t.plus : ObjectProperty (ModuleDerived X)) K.obj)
    (hφ : φ.hom.HasFiniteTorDimension) :
    IsIso (Hom.DerivedBaseChange.InternalHom.canonicalMap sq.toCommSq H_X H_X' T_X T_X' M K.obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.InternalHom
