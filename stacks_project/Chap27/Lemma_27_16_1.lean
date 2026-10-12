/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite

universe u

/- Lemma 27.16.1: for a positive degree, the functor associated to the pulled-back graded
algebra is canonically isomorphic to the fiber product of the original functor with the
functor of points of the new base. -/
@[stacks 01NT] #check
  (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorPullback.toPullbackIso :
    ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
      {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
      {d : ℕ} {g : S' ⟶ S}
      {F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d}
      (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorPullback g F_d),
      F'_d.toFunctor ≅ CategoryTheory.Limits.pullback
        (CategoryTheory.yoneda.map g) F_d.baseMap)

#check (CategoryTheory.Limits.pullback :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) [CategoryTheory.Limits.HasPullback f g],
    AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor :
  ∀ (S : AlgebraicGeometry.Scheme.{u})
    (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf)
    (d : ℕ), Type (u + 1))

#check (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctor :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d),
    AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.Scheme.RelativeProjGradedPullback :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}} (g : S' ⟶ S)
    (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf)
    (𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf),
    Type u)

#check (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorBaseChangeComparison :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S' 𝒜' d),
    Type (u + 1))

#check (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorPullback :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d),
    Type (u + 1))

#check (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIso :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison :
      AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorBaseChangeComparison
        g F_d 𝒜' F'_d),
    F'_d.toFunctor ≅
      AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctor g F_d)

#check (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorPullback.toBaseChangeIso :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} {g : S' ⟶ S}
    {F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d}
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorPullback g F_d),
    F'_d.toFunctor ≅
      AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctor g F_d)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctorIsoPullback :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d),
    AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctor g F_d ≅
      CategoryTheory.Limits.pullback (CategoryTheory.yoneda.map g) F_d.baseMap)

#check (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor.toFunctor :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d),
    AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor.baseMap :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d),
    F_d.toFunctor ⟶ CategoryTheory.yoneda.obj S)

#check (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor.degree_pos :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d),
    1 ≤ d)

#check (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor.algebra_isQuasicoherent :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (n : ℤ), (𝒜 n).IsQuasicoherent)

#check (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor.ofFunctor :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (toFunctor : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type u)
    (baseMap : toFunctor ⟶ CategoryTheory.yoneda.obj S)
    (degree_pos : 1 ≤ d)
    (algebra_isQuasicoherent : ∀ n : ℤ, (𝒜 n).IsQuasicoherent),
    AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)

#check (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor.pointOver :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (T : AlgebraicGeometry.Scheme.{u}ᵒᵖ)
    (t : (CategoryTheory.yoneda.obj S).obj T), Type u)

#check (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor.objIso :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (T : AlgebraicGeometry.Scheme.{u}ᵒᵖ),
    F_d.toFunctor.obj T ≃
      Σ t : (CategoryTheory.yoneda.obj S).obj T, F_d.pointOver T t)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeObj :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (T : AlgebraicGeometry.Scheme.{u}ᵒᵖ), Type u)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangePoint :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (T : AlgebraicGeometry.Scheme.{u}), Type u)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctorMap_property :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    {T T' : AlgebraicGeometry.Scheme.{u}ᵒᵖ} (a : T ⟶ T')
    (x : AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeObj g F_d T),
    (CategoryTheory.yoneda.obj S').map a x.1.1 ≫ g =
      F_d.baseMap.app T' (F_d.toFunctor.map a x.1.2))

#check (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctorMap :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    {T T' : AlgebraicGeometry.Scheme.{u}ᵒᵖ} (a : T ⟶ T'),
    AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeObj g F_d T →
      AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeObj g F_d T')

#check (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctorMap_id :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (T : AlgebraicGeometry.Scheme.{u}ᵒᵖ),
    AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctorMap g F_d (𝟙 T) = id)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctorMap_comp :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    {T T' T'' : AlgebraicGeometry.Scheme.{u}ᵒᵖ}
    (a : T ⟶ T') (b : T' ⟶ T''),
    AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctorMap g F_d (a ≫ b) =
      AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctorMap g F_d b ∘
        AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctorMap g F_d a)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctorMap_id_hom :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (T : AlgebraicGeometry.Scheme.{u}ᵒᵖ),
    TypeCat.ofHom
        (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctorMap g F_d (𝟙 T)) =
      𝟙 (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeObj g F_d T))

#check (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctorMap_comp_hom :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    {T T' T'' : AlgebraicGeometry.Scheme.{u}ᵒᵖ}
    (a : T ⟶ T') (b : T' ⟶ T''),
    TypeCat.ofHom
        (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctorMap g F_d (a ≫ b)) =
      TypeCat.ofHom
          (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctorMap g F_d a) ≫
        TypeCat.ofHom
          (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctorMap g F_d b))

#check (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S' 𝒜' d)
    (homEquiv : ∀ (T : AlgebraicGeometry.Scheme.{u}ᵒᵖ)
      (t : (CategoryTheory.yoneda.obj S').obj T),
      F'_d.pointOver T t ≃ F_d.pointOver T (t ≫ g))
    (T : AlgebraicGeometry.Scheme.{u}ᵒᵖ),
    F'_d.toFunctor.obj T →
      AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeObj g F_d T)

#check (AlgebraicGeometry.Scheme.pulledBackGradedAlgebraSection :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}} (g : S' ⟶ S)
    (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf)
    (n : ℤ) (U : (S'.Opens)ᵒᵖ), ModuleCat (S'.presheaf.obj U))

#check (AlgebraicGeometry.Scheme.RelativeProjGradedPullback.ofDegreeIso :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {g : S' ⟶ S}
    {𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf}
    (degreeIso : ∀ n : ℤ,
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (𝒜 n)) ≅ 𝒜' n)
    (pullbackOne : ∀ U : (S'.Opens)ᵒᵖ,
      AlgebraicGeometry.Scheme.pulledBackGradedAlgebraSection g 𝒜 0 U)
    (pullbackMul : ∀ (U : (S'.Opens)ᵒᵖ) (n m : ℤ),
      AlgebraicGeometry.Scheme.pulledBackGradedAlgebraSection g 𝒜 n U →ₗ[S'.presheaf.obj U]
        AlgebraicGeometry.Scheme.pulledBackGradedAlgebraSection g 𝒜 m U →ₗ[S'.presheaf.obj U]
          AlgebraicGeometry.Scheme.pulledBackGradedAlgebraSection g 𝒜 (n + m) U)
    (map_one : ∀ U : (S'.Opens)ᵒᵖ,
      (((degreeIso 0).hom.val.app U).hom) (pullbackOne U) = 𝒜'.one U)
    (map_mul : ∀ (U : (S'.Opens)ᵒᵖ) (n m : ℤ)
      (a : AlgebraicGeometry.Scheme.pulledBackGradedAlgebraSection g 𝒜 n U)
      (b : AlgebraicGeometry.Scheme.pulledBackGradedAlgebraSection g 𝒜 m U),
      (((degreeIso (n + m)).hom.val.app U).hom) (pullbackMul U n m a b) =
        𝒜'.mul U n m ((((degreeIso n).hom.val.app U).hom) a)
          ((((degreeIso m).hom.val.app U).hom) b)),
    AlgebraicGeometry.Scheme.RelativeProjGradedPullback g 𝒜 𝒜')

#check (AlgebraicGeometry.Scheme.RelativeProjGradedPullback.degreeMap :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {g : S' ⟶ S}
    {𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf}
    (pullback : AlgebraicGeometry.Scheme.RelativeProjGradedPullback g 𝒜 𝒜')
    (n : ℤ) (U : (S'.Opens)ᵒᵖ),
    AlgebraicGeometry.Scheme.pulledBackGradedAlgebraSection g 𝒜 n U →ₗ[S'.presheaf.obj U]
      (𝒜' n).val.obj U)

#check (AlgebraicGeometry.Scheme.RelativeProjGradedPullback.spec :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {g : S' ⟶ S}
    {𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf}
    (pullback : AlgebraicGeometry.Scheme.RelativeProjGradedPullback g 𝒜 𝒜'),
    (∀ U : (S'.Opens)ᵒᵖ,
      pullback.degreeMap 0 U (pullback.pullbackOne U) = 𝒜'.one U) ∧
    (∀ (U : (S'.Opens)ᵒᵖ) (n m : ℤ)
      (a : AlgebraicGeometry.Scheme.pulledBackGradedAlgebraSection g 𝒜 n U)
      (b : AlgebraicGeometry.Scheme.pulledBackGradedAlgebraSection g 𝒜 m U),
      pullback.degreeMap (n + m) U (pullback.pullbackMul U n m a b) =
        𝒜'.mul U n m (pullback.degreeMap n U a) (pullback.degreeMap m U b)))

#check (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorPullback.ofPointEquiv :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} {g : S' ⟶ S}
    {F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d}
    (algebra : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf)
    (toRelativeProjDegreeFunctor :
      AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S' algebra d)
    (comparison : AlgebraicGeometry.Scheme.RelativeProjGradedPullback g 𝒜 algebra)
    (pointEquiv : ∀ (T : AlgebraicGeometry.Scheme.{u}ᵒᵖ)
      (t : (CategoryTheory.yoneda.obj S').obj T),
      toRelativeProjDegreeFunctor.pointOver T t ≃ F_d.pointOver T (t ≫ g))
    (pointEquiv_natural : ∀ {T T' : AlgebraicGeometry.Scheme.{u}ᵒᵖ}
      (a : T ⟶ T'),
      toRelativeProjDegreeFunctor.toFunctor.map a ≫
          TypeCat.ofHom
            (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv
              g F_d algebra toRelativeProjDegreeFunctor pointEquiv T') =
        TypeCat.ofHom
            (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv
              g F_d algebra toRelativeProjDegreeFunctor pointEquiv T) ≫
          (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctor g F_d).map a),
    AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorPullback g F_d)

#check (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorPullback.toFunctor :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} {g : S' ⟶ S}
    {F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d}
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorPullback g F_d),
    AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorPullback.conditions_spec :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} {g : S' ⟶ S}
    {F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d}
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorPullback g F_d),
    ((∀ U : (S'.Opens)ᵒᵖ,
        F'_d.comparison.degreeMap 0 U (F'_d.comparison.pullbackOne U) =
          F'_d.algebra.one U) ∧
      (∀ (U : (S'.Opens)ᵒᵖ) (n m : ℤ)
        (a : AlgebraicGeometry.Scheme.pulledBackGradedAlgebraSection g 𝒜 n U)
        (b : AlgebraicGeometry.Scheme.pulledBackGradedAlgebraSection g 𝒜 m U),
        F'_d.comparison.degreeMap (n + m) U
            (F'_d.comparison.pullbackMul U n m a b) =
          F'_d.algebra.mul U n m (F'_d.comparison.degreeMap n U a)
            (F'_d.comparison.degreeMap m U b))) ∧
      ∀ {T T' : AlgebraicGeometry.Scheme.{u}ᵒᵖ} (a : T ⟶ T'),
        F'_d.toRelativeProjDegreeFunctor.toFunctor.map a ≫
            TypeCat.ofHom
              (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv
                g F_d F'_d.algebra F'_d.toRelativeProjDegreeFunctor
                  F'_d.pointEquiv T') =
          TypeCat.ofHom
              (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv
                g F_d F'_d.algebra F'_d.toRelativeProjDegreeFunctor
                  F'_d.pointEquiv T) ≫
            (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctor g F_d).map a)

#check (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorBaseChangeComparison.conditions_spec :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} {g : S' ⟶ S}
    {F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d}
    {𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf}
    {F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S' 𝒜' d}
    (comparison :
      AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorBaseChangeComparison
        g F_d 𝒜' F'_d),
    ((∀ U : (S'.Opens)ᵒᵖ,
        comparison.pullback.degreeMap 0 U (comparison.pullback.pullbackOne U) =
          𝒜'.one U) ∧
      (∀ (U : (S'.Opens)ᵒᵖ) (n m : ℤ)
        (a : AlgebraicGeometry.Scheme.pulledBackGradedAlgebraSection g 𝒜 n U)
        (b : AlgebraicGeometry.Scheme.pulledBackGradedAlgebraSection g 𝒜 m U),
        comparison.pullback.degreeMap (n + m) U
            (comparison.pullback.pullbackMul U n m a b) =
          𝒜'.mul U n m (comparison.pullback.degreeMap n U a)
            (comparison.pullback.degreeMap m U b))) ∧
      ∀ {T T' : AlgebraicGeometry.Scheme.{u}ᵒᵖ} (a : T ⟶ T'),
        F'_d.toFunctor.map a ≫
            TypeCat.ofHom
              (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv
                g F_d 𝒜' F'_d comparison.pointEquiv T') =
          TypeCat.ofHom
              (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv
                g F_d 𝒜' F'_d comparison.pointEquiv T) ≫
            (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctor g F_d).map a)

#check (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorPullback.toBaseChangeComparison :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} {g : S' ⟶ S}
    {F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d}
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorPullback g F_d),
    AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorBaseChangeComparison
      g F_d F'_d.algebra F'_d.toRelativeProjDegreeFunctor)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoHomApp :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison :
      AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorBaseChangeComparison
        g F_d 𝒜' F'_d)
    (T : AlgebraicGeometry.Scheme.{u}ᵒᵖ),
    F'_d.toFunctor.obj T →
      AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeObj g F_d T)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoInvApp :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison :
      AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorBaseChangeComparison
        g F_d 𝒜' F'_d)
    (T : AlgebraicGeometry.Scheme.{u}ᵒᵖ),
    AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeObj g F_d T →
      F'_d.toFunctor.obj T)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIso_hom_naturality :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison :
      AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorBaseChangeComparison
        g F_d 𝒜' F'_d)
    {T T' : AlgebraicGeometry.Scheme.{u}ᵒᵖ} (a : T ⟶ T'),
    F'_d.toFunctor.map a ≫
        TypeCat.ofHom
          (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoHomApp
            g F_d 𝒜' F'_d comparison T') =
      TypeCat.ofHom
          (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoHomApp
            g F_d 𝒜' F'_d comparison T) ≫
        (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctor g F_d).map a)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIso_inv_naturality :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison :
      AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorBaseChangeComparison
        g F_d 𝒜' F'_d)
    {T T' : AlgebraicGeometry.Scheme.{u}ᵒᵖ} (a : T ⟶ T'),
    (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctor g F_d).map a ≫
        TypeCat.ofHom
          (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoInvApp
            g F_d 𝒜' F'_d comparison T') =
      TypeCat.ofHom
          (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoInvApp
            g F_d 𝒜' F'_d comparison T) ≫
        F'_d.toFunctor.map a)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoHom :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison :
      AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorBaseChangeComparison
        g F_d 𝒜' F'_d),
    F'_d.toFunctor ⟶
      AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctor g F_d)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoInv :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison :
      AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorBaseChangeComparison
        g F_d 𝒜' F'_d),
    AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctor g F_d ⟶
      F'_d.toFunctor)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIso_hom_inv_id :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison :
      AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorBaseChangeComparison
        g F_d 𝒜' F'_d),
    AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoHom
          g F_d 𝒜' F'_d comparison ≫
        AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoInv
          g F_d 𝒜' F'_d comparison =
      𝟙 F'_d.toFunctor)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIso_inv_hom_id :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison :
      AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorBaseChangeComparison
        g F_d 𝒜' F'_d),
    AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoInv
          g F_d 𝒜' F'_d comparison ≫
        AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoHom
          g F_d 𝒜' F'_d comparison =
      𝟙 (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctor g F_d))

#check (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeObjIsoPullback :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (T : AlgebraicGeometry.Scheme.{u}ᵒᵖ),
    AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeObj g F_d T ≅
      (CategoryTheory.Limits.pullback
        (CategoryTheory.yoneda.map g) F_d.baseMap).obj T)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeObjIsoPullback_naturality :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    {T T' : AlgebraicGeometry.Scheme.{u}ᵒᵖ} (a : T ⟶ T'),
    (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeFunctor g F_d).map a ≫
        (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeObjIsoPullback
          g F_d T').hom =
      (AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeObjIsoPullback
        g F_d T).hom ≫
        (CategoryTheory.Limits.pullback
          (CategoryTheory.yoneda.map g) F_d.baseMap).map a)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIso_hom :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison :
      AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorBaseChangeComparison
        g F_d 𝒜' F'_d),
    (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIso
      g F_d 𝒜' F'_d comparison).hom =
        AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoHom
          g F_d 𝒜' F'_d comparison)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIso_inv :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison :
      AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorBaseChangeComparison
        g F_d 𝒜' F'_d),
    (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIso
      g F_d 𝒜' F'_d comparison).inv =
        AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoInv
          g F_d 𝒜' F'_d comparison)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIso_homApp :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison :
      AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorBaseChangeComparison
        g F_d 𝒜' F'_d)
    (T : AlgebraicGeometry.Scheme.{u}ᵒᵖ) (x : F'_d.toFunctor.obj T),
    (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIso
      g F_d 𝒜' F'_d comparison).hom.app T x =
        AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoHomApp
          g F_d 𝒜' F'_d comparison T x)

#check (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIso_invApp :
  ∀ {S S' : AlgebraicGeometry.Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf}
    {d : ℕ} (g : S' ⟶ S)
    (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison :
      AlgebraicGeometry.Scheme.RelativeProjDegreeFunctorBaseChangeComparison
        g F_d 𝒜' F'_d)
    (T : AlgebraicGeometry.Scheme.{u}ᵒᵖ)
    (x : AlgebraicGeometry.Scheme.relativeProjDegreeBaseChangeObj g F_d T),
    (AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIso
      g F_d 𝒜' F'_d comparison).inv.app T x =
        AlgebraicGeometry.Scheme.relativeProjDegreeFunctorBaseChangeIsoInvApp
          g F_d 𝒜' F'_d comparison T x)
