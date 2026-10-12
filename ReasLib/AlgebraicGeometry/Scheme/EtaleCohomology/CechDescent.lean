/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianPullback
public import ReasLib.AlgebraicTopology.Cech.Nerve.LowDegree
public import ReasLib.CategoryTheory.Homology.SpectralSequence.FiniteAbutment
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Acyclicity

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicTopology
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [(Arrow.mk f).HasCechNerve]

/-- The Čech nerve of a scheme morphism, as a simplicial scheme. -/
abbrev finiteCechNerve : SimplicialObject Scheme.{u} :=
  (Arrow.mk f).cechNerve

/-- The degree-`n` scheme `X_n` in the Čech nerve of `f`, the `(n + 1)`-fold fibre product of
`X` over `Y`. -/
abbrev finiteCechScheme (n : ℕ) : Scheme.{u} :=
  (finiteCechNerve f).obj (op ⦋n⦌)

/-- The structure map `f_n : X_n ⟶ Y` of a Čech-nerve degree. -/
abbrev finiteCechMap (n : ℕ) : finiteCechScheme f n ⟶ Y :=
  Arrow.cechNerve.base (Arrow.mk f) (op ⦋n⦌)

/-- Degree zero of the Čech nerve of `f` is canonically `X`. -/
abbrev finiteCechScheme_zero : finiteCechScheme f 0 ≅ X :=
  Arrow.cechNerve.degreeZero.iso (Arrow.mk f)

/-- The degree-zero structure map recovers `f` after the canonical identification `X_0 ≅ X`. -/
theorem finiteCechMap_zero :
    (finiteCechScheme_zero f).inv ≫ finiteCechMap f 0 = f :=
  Arrow.cechNerve.degreeZero.inv_base (Arrow.mk f)

/-- A simplex operator acts on Čech-nerve schemes by the simplicial structure maps. -/
abbrev finiteCechNerve_map {n m : SimplexCategory} (α : n ⟶ m) :
    finiteCechScheme f m.len ⟶ finiteCechScheme f n.len :=
  (finiteCechNerve f).map α.op

/-- Čech-nerve operators are morphisms over `Y`. -/
theorem finiteCechNerve_map_comp_base {n m : SimplexCategory} (α : n ⟶ m) :
    finiteCechNerve_map f α ≫ finiteCechMap f n.len = finiteCechMap f m.len :=
  Arrow.cechNerve.map_base (Arrow.mk f) α.op

/-- The inverse image `f_n⁻¹ F` of an abelian étale sheaf along a Čech-nerve projection. -/
abbrev finiteCechInverseImage (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf (finiteCechScheme f n).smallEtaleTopology AddCommGrpCat.{u} :=
  (abelianInverseImage (finiteCechMap f n)).obj F

/-- The sheaf `F_n = f_{n,*} f_n⁻¹ F` on `Y.smallEtaleTopology`. -/
abbrev finiteCechSheaf (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  ((smallEtalePullback (finiteCechMap f n)).sheafPushforwardContinuous AddCommGrpCat.{u}
    Y.smallEtaleTopology (finiteCechScheme f n).smallEtaleTopology).obj
      (finiteCechInverseImage f F n)

/-- The adjunction unit `F ⟶ f_{n,*} f_n⁻¹ F`. -/
abbrev finiteCech_unit (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    F ⟶ finiteCechSheaf f F n :=
  (abelianAdjunctionDirectImage (finiteCechMap f n)).unit.app F

/-- The canonical augmentation `F ⟶ F_0`. -/
abbrev finiteCech_augmentation (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    F ⟶ finiteCechSheaf f F 0 :=
  finiteCech_unit f F 0

/-- The site-functor isomorphism for a Čech-nerve operator over `Y`. -/
abbrev finiteCech_pullbackCompIso {n m : SimplexCategory} (α : n ⟶ m) :
    smallEtalePullback (finiteCechMap f m.len) ≅
      smallEtalePullback (finiteCechMap f n.len) ⋙
        smallEtalePullback (finiteCechNerve_map f α) :=
  MorphismProperty.Over.pullbackComp
    (finiteCechNerve_map f α) (finiteCechMap f n.len)
    (finiteCechMap f m.len) (finiteCechNerve_map_comp_base f α).symm

/-- The sequential inverse image along a Čech-nerve operator. -/
abbrev finiteCechInverseImage_comp (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    {n m : SimplexCategory} (α : n ⟶ m) :
    Sheaf (finiteCechScheme f m.len).smallEtaleTopology AddCommGrpCat.{u} :=
  (abelianInverseImage (finiteCechNerve_map f α)).obj
    (finiteCechInverseImage f F n.len)

/-- The identification `g⁻¹ f_n⁻¹ F ≅ f_m⁻¹ F` for a Čech-nerve operator `g`. -/
noncomputable def finiteCechInverseImage_iso
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) {n m : SimplexCategory} (α : n ⟶ m) :
    finiteCechInverseImage_comp f F α ≅ finiteCechInverseImage f F m.len :=
  let Fn := smallEtalePullback (finiteCechMap f n.len)
  let G := smallEtalePullback (finiteCechNerve_map f α)
  let hcomp := Functor.isContinuous_comp Fn G Y.smallEtaleTopology
    (finiteCechScheme f n.len).smallEtaleTopology
    (finiteCechScheme f m.len).smallEtaleTopology
  let adjFn := abelianAdjunctionDirectImage (finiteCechMap f n.len)
  let adjG := abelianAdjunctionDirectImage (finiteCechNerve_map f α)
  let adjSeq := (adjFn.comp adjG).ofNatIsoRight
    (Functor.sheafPushforwardContinuousComp Fn G AddCommGrpCat.{u}
      Y.smallEtaleTopology (finiteCechScheme f n.len).smallEtaleTopology
      (finiteCechScheme f m.len).smallEtaleTopology)
  let adjFm := abelianAdjunctionDirectImage (finiteCechMap f m.len)
  let adjFm' := adjFm.ofNatIsoRight
    (@Functor.sheafPushforwardContinuousIso _ _ _ _ _ _
      (finiteCech_pullbackCompIso f α) AddCommGrpCat.{u} inferInstance
      Y.smallEtaleTopology (finiteCechScheme f m.len).smallEtaleTopology
      inferInstance hcomp)
  (Adjunction.leftAdjointUniq adjSeq adjFm').app F

/-- The face-induced map `F_n ⟶ F_m` of Čech sheaves on `Y_étale`. -/
noncomputable def finiteCechSheaf_map
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) {n m : SimplexCategory} (α : n ⟶ m) :
    finiteCechSheaf f F n.len ⟶ finiteCechSheaf f F m.len :=
  let G := smallEtalePullback (finiteCechNerve_map f α)
  let Fn := smallEtalePullback (finiteCechMap f n.len)
  let hcomp := Functor.isContinuous_comp Fn G Y.smallEtaleTopology
    (finiteCechScheme f n.len).smallEtaleTopology
    (finiteCechScheme f m.len).smallEtaleTopology
  (Fn.sheafPushforwardContinuous AddCommGrpCat.{u}
      Y.smallEtaleTopology (finiteCechScheme f n.len).smallEtaleTopology).map
    ((abelianAdjunctionDirectImage (finiteCechNerve_map f α)).unit.app
      (finiteCechInverseImage f F n.len)) ≫
    (Functor.sheafPushforwardContinuousComp Fn G AddCommGrpCat.{u}
        Y.smallEtaleTopology (finiteCechScheme f n.len).smallEtaleTopology
        (finiteCechScheme f m.len).smallEtaleTopology).hom.app
      (finiteCechInverseImage_comp f F α) ≫
    (@Functor.sheafPushforwardContinuousIso _ _ _ _ _ _
        (finiteCech_pullbackCompIso f α).symm AddCommGrpCat.{u} inferInstance
        Y.smallEtaleTopology (finiteCechScheme f m.len).smallEtaleTopology
        hcomp inferInstance).hom.app
      (finiteCechInverseImage_comp f F α) ≫
    ((smallEtalePullback (finiteCechMap f m.len)).sheafPushforwardContinuous AddCommGrpCat.{u}
        Y.smallEtaleTopology (finiteCechScheme f m.len).smallEtaleTopology).map
      (finiteCechInverseImage_iso f F α).hom

/-- Identity simplex operators induce identity maps of Čech sheaves. -/
theorem finiteCechSheaf_map_id (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (n : SimplexCategory) :
    finiteCechSheaf_map f F (𝟙 n) = 𝟙 (finiteCechSheaf f F n.len) :=
  sorry

/-- Čech-sheaf transition maps are functorial in simplex operators. -/
theorem finiteCechSheaf_map_comp (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    {n m k : SimplexCategory} (α : n ⟶ m) (β : m ⟶ k) :
    finiteCechSheaf_map f F (α ≫ β) =
      finiteCechSheaf_map f F α ≫ finiteCechSheaf_map f F β :=
  sorry

/-- The cosimplicial abelian sheaf `n ↦ F_n` on `Y_étale`. -/
noncomputable def finiteCechCosimplicial (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    CosimplicialObject (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) where
  obj n := finiteCechSheaf f F n.len
  map α := finiteCechSheaf_map f F α
  map_id n := finiteCechSheaf_map_id f F n
  map_comp α β := finiteCechSheaf_map_comp f F α β

variable [Abelian (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]

/-- The objects of the augmented alternating Čech complex: `F` in degree `0` and `F_{n-1}` afterwards. -/
abbrev finiteCechComplex_X (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    ℕ → Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}
  | 0 => F
  | n + 1 => finiteCechSheaf f F n

/-- The differentials of the augmented alternating Čech complex. -/
noncomputable def finiteCechComplex_d (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    ∀ n, finiteCechComplex_X f F n ⟶ finiteCechComplex_X f F (n + 1)
  | 0 => finiteCech_augmentation f F
  | n + 1 => AlternatingCofaceMapComplex.objD (finiteCechCosimplicial f F) n

/-- Consecutive differentials of the augmented Čech complex compose to zero. -/
theorem finiteCechComplex_d_squared (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (n : ℕ) :
    finiteCechComplex_d f F n ≫ finiteCechComplex_d f F (n + 1) = 0 :=
  sorry

/-- The augmented alternating cochain complex `F → F_0 → F_1 → ⋯` on `Y_étale`. -/
noncomputable def finiteCechComplex (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ℕ :=
  CochainComplex.of (finiteCechComplex_X f F) (finiteCechComplex_d f F)
    (finiteCechComplex_d_squared f F)

/-- Degree zero of the augmented complex is `F`. -/
theorem finiteCechComplex_X_zero (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (finiteCechComplex f F).X 0 = F :=
  rfl

/-- Positive degrees of the augmented complex are the Čech sheaves `F_n`. -/
theorem finiteCechComplex_X_succ (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    (finiteCechComplex f F).X (n + 1) = finiteCechSheaf f F n :=
  rfl

/-- The first-page target `H^q_étale(X_p, f_p⁻¹ F)`. -/
abbrev finiteCech_pageOne (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    [∀ n : ℕ, HasSheafify (finiteCechScheme f n).smallEtaleTopology AddCommGrpCat.{u}]
    [∀ n : ℕ, Abelian (Sheaf (finiteCechScheme f n).smallEtaleTopology AddCommGrpCat.{u})]
    [∀ n : ℕ,
      HasInjectiveResolutions (Sheaf (finiteCechScheme f n).smallEtaleTopology AddCommGrpCat.{u})]
    [∀ n : ℕ, HasTerminal (finiteCechScheme f n).Etale]
    [∀ n : ℕ,
      (siteAbelianSectionsFunctor (finiteCechScheme f n).smallEtaleTopology
        (terminal (finiteCechScheme f n).Etale)).Additive]
    (p q : ℕ) :
    AddCommGrpCat.{u} :=
  ((siteAbelianSectionsFunctor (finiteCechScheme f p).smallEtaleTopology
    (terminal (finiteCechScheme f p).Etale)).rightDerived q).obj
      (finiteCechInverseImage f F p)

/-- The abutment target `H^n_étale(Y, F)`. -/
abbrev finiteCech_abutment (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal Y.Etale]
    [(siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale)).Additive]
    (n : ℕ) :
    AddCommGrpCat.{u} :=
  ((siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale)).rightDerived n).obj F

/-- The finite Čech complex is exact for a finite surjective morphism. -/
theorem finiteCechComplex_exact [IsFinite f] [Surjective f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (finiteCechComplex f F).Acyclic :=
  sorry

/-- The finite Čech spectral sequence has first page `H^q_étale(X_p, f_p⁻¹ F)` and abutment
`H^(p+q)_étale(Y, F)`. -/
theorem finiteCech_spectralSequence [IsFinite f] [Surjective f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal Y.Etale]
    [(siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale)).Additive]
    [∀ n : ℕ, HasSheafify (finiteCechScheme f n).smallEtaleTopology AddCommGrpCat.{u}]
    [∀ n : ℕ, Abelian (Sheaf (finiteCechScheme f n).smallEtaleTopology AddCommGrpCat.{u})]
    [∀ n : ℕ,
      HasInjectiveResolutions (Sheaf (finiteCechScheme f n).smallEtaleTopology AddCommGrpCat.{u})]
    [∀ n : ℕ, HasTerminal (finiteCechScheme f n).Etale]
    [∀ n : ℕ,
      (siteAbelianSectionsFunctor (finiteCechScheme f n).smallEtaleTopology
        (terminal (finiteCechScheme f n).Etale)).Additive]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅ finiteCech_pageOne f F p q),
      CohomologicalSpectralSequenceNat.FinitelyAbutsTo E (finiteCech_abutment F) :=
  sorry

/-- The finite Čech spectral sequence is functorial in the coefficient sheaf. -/
theorem finiteCech_spectralSequence_functorial [IsFinite f] [Surjective f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal Y.Etale]
    [(siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale)).Additive]
    [∀ n : ℕ, HasSheafify (finiteCechScheme f n).smallEtaleTopology AddCommGrpCat.{u}]
    [∀ n : ℕ, Abelian (Sheaf (finiteCechScheme f n).smallEtaleTopology AddCommGrpCat.{u})]
    [∀ n : ℕ,
      HasInjectiveResolutions (Sheaf (finiteCechScheme f n).smallEtaleTopology AddCommGrpCat.{u})]
    [∀ n : ℕ, HasTerminal (finiteCechScheme f n).Etale]
    [∀ n : ℕ,
      (siteAbelianSectionsFunctor (finiteCechScheme f n).smallEtaleTopology
        (terminal (finiteCechScheme f n).Etale)).Additive] :
    ∃ (E : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
      CohomologicalSpectralSequenceNat AddCommGrpCat.{u} 1)
      (pageOneIso : ∀ (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (p q : ℕ),
        ((E.obj F).page 1 le_rfl).X (p, q) ≅ finiteCech_pageOne f F p q)
      (pageOneNaturality : ∀ {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}}
        (α : F ⟶ G) (p q : ℕ),
        ((E.map α).hom 1 le_rfl).f (p, q) ≫ (pageOneIso G p q).hom =
          (pageOneIso F p q).hom ≫
            ((siteAbelianSectionsFunctor (finiteCechScheme f p).smallEtaleTopology
                (terminal (finiteCechScheme f p).Etale)).rightDerived q).map
              ((abelianInverseImage (finiteCechMap f p)).map α)),
      (∀ F, CohomologicalSpectralSequenceNat.FinitelyAbutsTo (E.obj F)
        (finiteCech_abutment F)) :=
  sorry

end AlgebraicGeometry.Scheme.Etale
