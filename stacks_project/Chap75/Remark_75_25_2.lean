/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport
public import stacks_project.Chap75.Lemma_75_7_3_ProperOver
public import stacks_project.Chap75.Lemma_75_20_5_InternalHom
public import stacks_project.Chap75.Lemma_75_25_7_GlobalSections
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Finite projective models for derived global sections over a ring

If `X` is of finite presentation over a ring `R` and `G` is a finitely presented
`𝒪_X`-module, flat over `R`, with support proper over `R`, then `RΓ(X, G)` is
perfect in `D(R)`. After cartesian affine base change along `specMap` of
`algebraMap R R'`, derived global sections of the base-changed module identify in
`D(R')` with the scalar extension of `RΓ(X, G)`, hence with `M ⊗_R R'` for a
finite projective model `M` of `RΓ(X, G)`, functorially in the `R`-algebra `R'`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open AlgebraicGeometry.AlgebraicSpace.Hom TopologicalSpace ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {R : Type u} [CommRing R]
variable {X : AlgebraicSpace (Spec (CommRingCat.of R))}

/-- Derived global sections `RΓ(X, G)` of a module concentrated in degree `0`, as an
object of `D(R)`. -/
abbrev affineModuleDerivedGlobalSections (G : X.Modules) :
    DerivedCategory (ModuleCat.{u} R) :=
  (globalSectionsOver (toBase X)).obj
    ((DerivedCategory.singleFunctor (Modules X) 0).obj G)

/-- `affineModuleDerivedGlobalSections G` is `globalSectionsOver (toBase X)` applied to
`G` placed in degree `0`. -/
theorem affineModuleDerivedGlobalSections_obj (G : X.Modules) :
    affineModuleDerivedGlobalSections G =
      (globalSectionsOver (toBase X)).obj
        ((DerivedCategory.singleFunctor (Modules X) 0).obj G) :=
  sorry

/-- The two presentation restrictions agree on the global-sections map of the chosen
atlas of `ofOver (Spec.map σ)` over `Spec B`. -/
theorem specMapGlobalSections_equalizes {A B : Type u} [CommRing A] [CommRing B]
    (σ : A →+* B) :
    ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
          (Yoneda.fullyFaithful.preimage
            (chosenPresentation
              (ofOver (Over.mk (Spec.map (CommRingCat.ofHom σ))))).atlas).left.appTop) ≫
        (chosenPresentation
          (ofOver (Over.mk (Spec.map (CommRingCat.ofHom σ))))).tAppTop =
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
          (Yoneda.fullyFaithful.preimage
            (chosenPresentation
              (ofOver (Over.mk (Spec.map (CommRingCat.ofHom σ))))).atlas).left.appTop) ≫
        (chosenPresentation
          (ofOver (Over.mk (Spec.map (CommRingCat.ofHom σ))))).sAppTop :=
  sorry

/-- The ring map `R' →+* Γ(Spec R', 𝒪)` induced by viewing `Spec R'` as an algebraic
space over `Spec R` along `σ : R →+* R'`. -/
noncomputable def specMapGlobalSections {A B : Type u} [CommRing A] [CommRing B]
    (σ : A →+* B) :
    B →+* globalSectionsRing (ofOver (Over.mk (Spec.map (CommRingCat.ofHom σ)))) :=
  (equalizer.lift
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
        (Yoneda.fullyFaithful.preimage
          (chosenPresentation
            (ofOver (Over.mk (Spec.map (CommRingCat.ofHom σ))))).atlas).left.appTop)
      (specMapGlobalSections_equalizes σ)).hom

/-- After comparison with the chosen atlas, `specMapGlobalSections σ` recovers the
scheme-level global-sections map of the atlas morphism to `Spec B`. -/
theorem specMapGlobalSections_comp_ι {A B : Type u} [CommRing A] [CommRing B]
    (σ : A →+* B) :
    (globalSectionsRing_ι
        (ofOver (Over.mk (Spec.map (CommRingCat.ofHom σ))))).hom.comp
      (specMapGlobalSections σ) =
      Scheme.Hom.globalSectionsMap
        (Yoneda.fullyFaithful.preimage
          (chosenPresentation
            (ofOver (Over.mk (Spec.map (CommRingCat.ofHom σ))))).atlas).left :=
  sorry

/-- Derived global sections of `R(f')_* L(g')^* G` on `ofOver (Spec.map (algebraMap R R'))`,
viewed in `D(R')` by restriction of scalars along `specMapGlobalSections`. -/
noncomputable def affineModuleDerivedGlobalSectionsBaseChange
    {R' : Type u} [CommRing R'] [Algebra R R']
    {X' : AlgebraicSpace (Spec (CommRingCat.of R))}
    (g' : X' ⟶ X)
    (f' : X' ⟶ ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
    (G : X.Modules) :
    DerivedCategory (ModuleCat.{u} R') :=
  (ModuleCat.derivedRestrictionOfScalars (specMapGlobalSections (algebraMap R R'))).obj
    ((moduleDerivedGlobalSections
        (ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R')))))).obj
      ((Modules.pushforwardDerived f').obj
        ((modulePullbackDerived g').obj
          ((DerivedCategory.singleFunctor (Modules X) 0).obj G))))

/-- `affineModuleDerivedGlobalSectionsBaseChange` is derived restriction of scalars of
derived global sections of `R(f')_* L(g')^* G`. -/
theorem affineModuleDerivedGlobalSectionsBaseChange_obj
    {R' : Type u} [CommRing R'] [Algebra R R']
    {X' : AlgebraicSpace (Spec (CommRingCat.of R))}
    (g' : X' ⟶ X)
    (f' : X' ⟶ ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
    (G : X.Modules) :
    affineModuleDerivedGlobalSectionsBaseChange g' f' G =
      (ModuleCat.derivedRestrictionOfScalars
          (specMapGlobalSections (algebraMap R R'))).obj
        ((moduleDerivedGlobalSections
            (ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R')))))).obj
          ((Modules.pushforwardDerived f').obj
            ((modulePullbackDerived g').obj
              ((DerivedCategory.singleFunctor (Modules X) 0).obj G)))) :=
  sorry

/-- Remark 75.25.2 (1): if `X` is of finite presentation over a ring `R` and `G` is a
finitely presented `𝒪_X`-module, flat over `R`, with support proper over `R`, then
`RΓ(X, G)` is perfect in `D(R)`. A perfect object of `D(R)` is isomorphic to `Q(M)`
for a finite complex `M` of finite projective `R`-modules, which is the model in the
source identification `RΓ(X_{R'}, G_{R'}) = M ⊗_R R'`. -/
@[stacks 0A1Q]
theorem globalSectionsOver_isPerfect_of_finitePresentation
    [FinitePresentation (toBase X)] (G : X.Modules) [G.IsFinitePresentation]
    (hflat : ∀ x, flatOverAt G (toBase X) x)
    (hsupport : ClosedSubset.IsProperOver (toBase X)
      (Closeds.closure (moduleSupport G))) :
    DerivedCategory.IsPerfect (affineModuleDerivedGlobalSections G) :=
  sorry

/-- Remark 75.25.2 (2): under the same hypotheses, for every `R`-algebra `R'` and every
cartesian square along `specMap` of `algebraMap R R'`, scalar extension of `RΓ(X, G)`
is isomorphic in `D(R')` to derived global sections of the base-changed module
`R(f')_* L(g')^* G`. Together with a finite projective model `M` of `RΓ(X, G)`, this
is the functorial identification `RΓ(X_{R'}, G_{R'}) = M ⊗_R R'`. -/
@[stacks 0A1Q]
theorem globalSectionsOver_baseChange_isIso_of_finitePresentation
    [FinitePresentation (toBase X)] (G : X.Modules) [G.IsFinitePresentation]
    (hflat : ∀ x, flatOverAt G (toBase X) x)
    (hsupport : ClosedSubset.IsProperOver (toBase X)
      (Closeds.closure (moduleSupport G)))
    {R' : Type u} [CommRing R'] [Algebra R R']
    {X' : AlgebraicSpace (Spec (CommRingCat.of R))}
    (g' : X' ⟶ X)
    (f' : X' ⟶ ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
    (sq : IsPullback g' f' (toBase X)
      (specMap (CommRingCat.ofHom (algebraMap R R')))) :
    Nonempty
      ((ModuleCat.derivedExtensionOfScalars (algebraMap R R')).obj
          (affineModuleDerivedGlobalSections G) ≅
        affineModuleDerivedGlobalSectionsBaseChange g' f' G) :=
  sorry

/-- Under the same hypotheses, the geometric derived base-change comparison
`L(specMap)^* R(toBase)_* G ⟶ R(f')_* L(g')^* G` is an isomorphism. -/
theorem derivedBaseChange_single_isIso_of_finitePresentation
    [FinitePresentation (toBase X)] (G : X.Modules) [G.IsFinitePresentation]
    (hflat : ∀ x, flatOverAt G (toBase X) x)
    (hsupport : ClosedSubset.IsProperOver (toBase X)
      (Closeds.closure (moduleSupport G)))
    {R' : Type u} [CommRing R'] [Algebra R R']
    {X' : AlgebraicSpace (Spec (CommRingCat.of R))}
    (g' : X' ⟶ X)
    (f' : X' ⟶ ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
    [IsIso (modulePullbackDerived.compComparison f'
      (specMap (CommRingCat.ofHom (algebraMap R R'))))]
    [IsIso (modulePullbackDerived.compComparison g' (toBase X))]
    (sq : IsPullback g' f' (toBase X)
      (specMap (CommRingCat.ofHom (algebraMap R R')))) :
    IsIso ((DerivedBaseChange.map sq.toCommSq).app
      ((DerivedCategory.singleFunctor (Modules X) 0).obj G)) :=
  sorry

/-- A perfect derived global sections object `RΓ(X, G)` is isomorphic in `D(R)` to the
localization of a bounded complex of finite projective `R`-modules. -/
theorem exists_boundedFiniteProjective_globalSections
    [FinitePresentation (toBase X)] (G : X.Modules) [G.IsFinitePresentation]
    (hflat : ∀ x, flatOverAt G (toBase X) x)
    (hsupport : ClosedSubset.IsProperOver (toBase X)
      (Closeds.closure (moduleSupport G))) :
    ∃ M : CochainComplex (ModuleCat.{u} R) ℤ,
      CochainComplex.IsBoundedFiniteProjective M ∧
        Nonempty (affineModuleDerivedGlobalSections G ≅ DerivedCategory.Q.obj M) :=
  sorry

/-- After cartesian affine base change, derived global sections of the base-changed
module are isomorphic in `D(R')` to the localization of the underived scalar
extension of a finite projective model of `RΓ(X, G)`. -/
theorem affineModuleDerivedGlobalSectionsBaseChange_iso_extendScalars
    [FinitePresentation (toBase X)] (G : X.Modules) [G.IsFinitePresentation]
    (hflat : ∀ x, flatOverAt G (toBase X) x)
    (hsupport : ClosedSubset.IsProperOver (toBase X)
      (Closeds.closure (moduleSupport G)))
    {R' : Type u} [CommRing R'] [Algebra R R']
    {X' : AlgebraicSpace (Spec (CommRingCat.of R))}
    (g' : X' ⟶ X)
    (f' : X' ⟶ ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
    (sq : IsPullback g' f' (toBase X)
      (specMap (CommRingCat.ofHom (algebraMap R R'))))
    (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (hM : CochainComplex.IsBoundedFiniteProjective M)
    (e : affineModuleDerivedGlobalSections G ≅ DerivedCategory.Q.obj M) :
    Nonempty
      (affineModuleDerivedGlobalSectionsBaseChange g' f' G ≅
        DerivedCategory.Q.obj
          (((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex
              (up ℤ)).obj M)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
