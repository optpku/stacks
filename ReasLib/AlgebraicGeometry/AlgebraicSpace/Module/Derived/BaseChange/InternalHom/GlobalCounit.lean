/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.AffineBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.InternalHom.Canonical

/-! # Scalar-valued derived Hom and counits under affine base change -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange.GlobalHom

/-- Global derived Hom, with coefficients supplied by a morphism to an affine scheme. -/
def obj {S : Scheme.{u}} {X : AlgebraicSpace S} {A : CommRingCat.{u}}
    {a : Spec A ⟶ S} (f : X ⟶ ofOver (Over.mk a)) (M K : ModuleDerived X) :
    DerivedCategory (ModuleCat.{u} A) :=
  (Modules.AffineGlobalSections.functor f).obj ((ModuleDerived.InternalHom.functor M).obj K)

variable {A B : CommRingCat.{u}} {φ : A ⟶ B}
variable {X X' : AlgebraicSpace (Spec A)} {g' : X' ⟶ X}
variable {f' : X' ⟶ ofOver (Over.mk (Spec.map φ))}
variable {f : X ⟶ ofOver (Over.mk (𝟙 (Spec A)))}

/-- The scalar-valued derived Hom base-change map is global scalar base change followed
by global sections of the canonical pullback–Hom comparison. -/
def map (sq : CommSq g' f' f (Hom.specMap φ)) (M K : ModuleDerived X) :
    (ModuleCat.derivedExtensionOfScalars φ.hom).obj (obj f M K) ⟶
      obj f' ((ModuleDerived.pullback g').obj M) ((ModuleDerived.pullback g').obj K) :=
  Modules.AffineGlobalSections.pullbackMap sq ((ModuleDerived.InternalHom.functor M).obj K) ≫
    (Modules.AffineGlobalSections.functor f').map
      (ModuleDerived.InternalHom.canonicalPullbackComparison g' M K)

/-- Relative sheaf Hom and global sections after direct image identify global derived
Hom into a direct image with scalar restriction of global derived Hom after pullback. -/
def adjunctionIso (sq : CommSq g' f' f (Hom.specMap φ))
    (M : ModuleDerived X) (L : ModuleDerived X') :
    obj f M ((Modules.moduleDerivedPushforward g').obj L) ≅
      (ModuleCat.derivedRestrictionOfScalars φ.hom).obj
        (obj f' ((ModuleDerived.pullback g').obj M) L) :=
  (Modules.AffineGlobalSections.functor f).mapIso
      (ModuleDerived.InternalHom.canonicalAdjunctionComparisonIso g' M L) ≪≫
    (Modules.AffineGlobalSections.pushforwardIso sq).app
      ((ModuleDerived.InternalHom.functor ((ModuleDerived.pullback g').obj M)).obj L)

/-- Applying global derived Hom to the geometric pullback–pushforward counit gives
the target counit edge. -/
def adjunctionCounitMap (g' : X' ⟶ X)
    (f' : X' ⟶ ofOver (Over.mk (Spec.map φ))) (M : ModuleDerived X) (L : ModuleDerived X') :
    obj f' ((ModuleDerived.pullback g').obj M)
        ((ModuleDerived.pullback g').obj ((Modules.moduleDerivedPushforward g').obj L)) ⟶
      obj f' ((ModuleDerived.pullback g').obj M) L :=
  (Modules.AffineGlobalSections.functor f').map
    ((ModuleDerived.InternalHom.functor ((ModuleDerived.pullback g').obj M)).map
      ((AlgebraicSpace.derivedPullbackPushforwardAdjunction g').counit.app L))

/-- Multiplication is scalar extension of the relative global Hom identification
followed by the extension–restriction adjunction counit. -/
def multiplication (sq : CommSq g' f' f (Hom.specMap φ))
    (M : ModuleDerived X) (L : ModuleDerived X') :
    (ModuleCat.derivedExtensionOfScalars φ.hom).obj
        (obj f M ((Modules.moduleDerivedPushforward g').obj L)) ⟶
      obj f' ((ModuleDerived.pullback g').obj M) L :=
  (ModuleCat.derivedExtensionOfScalars φ.hom).map (adjunctionIso sq M L).hom ≫
    (ModuleCat.derivedExtensionRestrictionAdjunction φ.hom).counit.app
      (obj f' ((ModuleDerived.pullback g').obj M) L)

end AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange.GlobalHom

namespace AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.GlobalHom

/-- For an affine Tor-independent cartesian square of quasi-compact quasi-separated
algebraic spaces, global derived Hom base change commutes with the geometric counit
and scalar multiplication. -/
theorem map_counit_commSq {A B : CommRingCat.{u}} (φ : A ⟶ B)
    {X X' : AlgebraicSpace (Spec A)} (g' : X' ⟶ X)
    (f' : X' ⟶ ofOver (Over.mk (Spec.map φ)))
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec A))))
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [IsQuasiCompact X'] [IsQuasiSeparated X']
    [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f (Hom.specMap φ))
    (hTor : TorIndependentOver (Over.mk f) (Over.mk (Hom.specMap φ)))
    (M : ModuleDerived X) (L : ModuleDerived X') :
    CommSq
      (Hom.DerivedBaseChange.GlobalHom.map sq.toCommSq M
        ((Modules.moduleDerivedPushforward g').obj L))
      (Hom.DerivedBaseChange.GlobalHom.multiplication sq.toCommSq M L)
      (Hom.DerivedBaseChange.GlobalHom.adjunctionCounitMap g' f' M L)
      (𝟙 _) := sorry

end AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.GlobalHom
