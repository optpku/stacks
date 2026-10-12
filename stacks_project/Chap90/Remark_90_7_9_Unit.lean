/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.ULift
public import stacks_project.Chap90.Definition_90_7_3
public import stacks_project.Chap90.Remark_90_7_6_TypesCompletion
public import stacks_project.Chap90.Remark_90_7_7_Can
public import stacks_project.Chap90.Remark_90_7_9_Restrict
public import stacks_project.Chap90.Remarks_90_5_2_Pushforward

/-!
# Unit and counit of completion versus restriction

The unit `G ⟶ hat(G|_{C_Λ})` sends an object `ξ` over a complete local algebra `R` to the
formal object of chosen pushforwards of `ξ` to the truncations `R ⧸ m_R^{n+1}`. The counit
`hat F |_{C_Λ} ⟶ F` is the evaluation functor `can` of Remark 90.7.7, after identifying
`RestrictInclusion` of the completion with `FormalObject.Restrict`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat CompleteLocalAlgCat Functor IsLocalRing
open scoped BasedFunctor

noncomputable section

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FormalObject

/-- The canonical projection from a complete local algebra to the included `n`th
maximal-adic truncation. -/
def truncationToInclusion (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    R ⟶ inclusion.obj (R.truncation n) where
  hom := Ideal.Quotient.mkₐ Λ (maximalIdeal R.carrier ^ (n + 1))
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `truncationToInclusion` is the quotient map. -/
theorem truncationToInclusion_hom (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (truncationToInclusion R n).hom =
      Ideal.Quotient.mkₐ Λ (maximalIdeal R.carrier ^ (n + 1)) := sorry

end FormalObject

namespace CategoryTheory.BasedCategory.RestrictInclusion

variable
  {X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)}

/-- Hom-universe lift of `RestrictInclusion X`, matching the object/hom constraint of
`FormalObject`. -/
abbrev total (X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)) :
    Type (max (u + 1) v) :=
  ULiftHom.{max (u + 1) v} (RestrictInclusion X)

/-- `total X` is the Hom-universe lift of `RestrictInclusion X`. -/
theorem total_eq :
    total X = ULiftHom.{max (u + 1) v} (RestrictInclusion X) := sorry

/-- Projection of the Hom-universe lift to `C_Λ`. -/
def projectionTotal (X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)) :
    total X ⥤ ArtinianLocalAlgCat Λ k :=
  (ULiftHom.down : total X ⥤ RestrictInclusion X) ⋙ projection X

/-- The lifted projection is the ordinary projection after forgetting the Hom lift. -/
theorem projectionTotal_eq :
    projectionTotal X =
      (ULiftHom.down : total X ⥤ RestrictInclusion X) ⋙ projection X := sorry

/-- The lifted restricted projection is cofibered in groupoids. -/
instance projectionTotal_op_isFiberedInGroupoids
    (X : BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k))
    [IsFibered.InGroupoids X.p.op] :
    IsFibered.InGroupoids (projectionTotal X).op := sorry

variable {S : Type v} [Category.{v} S]
variable {proj : S ⥤ ArtinianLocalAlgCat Λ k} [IsFibered.InGroupoids proj.op]

/-- Convert a restriction of the completion to a `FormalObject.Restrict`. -/
def toFormalRestrict
    (ξ : RestrictInclusion (BasedCategory.ofFunctor (completion proj))) :
    FormalObject.Restrict proj where
  formal := ξ.obj
  base := ξ.base
  over := ξ.over

/-- Convert a `FormalObject.Restrict` to a restriction of the completion. -/
def ofFormalRestrict (ξ : FormalObject.Restrict proj) :
    RestrictInclusion (BasedCategory.ofFunctor (completion proj)) where
  obj := ξ.formal
  base := ξ.base
  over := ξ.over

/-- `toFormalRestrict` preserves the stored formal object. -/
theorem toFormalRestrict_formal
    (ξ : RestrictInclusion (BasedCategory.ofFunctor (completion proj))) :
    (toFormalRestrict ξ).formal = ξ.obj := sorry

/-- `ofFormalRestrict` preserves the stored formal object. -/
theorem ofFormalRestrict_obj (ξ : FormalObject.Restrict proj) :
    (ofFormalRestrict ξ).obj = ξ.formal := sorry

/-- Functor converting restrictions of the completion into `FormalObject.Restrict`. -/
def toFormalRestrictFunctor :
    RestrictInclusion (BasedCategory.ofFunctor (completion proj)) ⥤
      FormalObject.Restrict proj where
  obj ξ := toFormalRestrict ξ
  map a :=
    { formal := a.obj
      base := a.base
      over := a.over }
  map_id := sorry
  map_comp := sorry

/-- Functor converting `FormalObject.Restrict` into restrictions of the completion. -/
def ofFormalRestrictFunctor :
    FormalObject.Restrict proj ⥤
      RestrictInclusion (BasedCategory.ofFunctor (completion proj)) where
  obj ξ := ofFormalRestrict ξ
  map a :=
    { obj := a.formal
      base := a.base
      over := a.over }
  map_id := sorry
  map_comp := sorry

end CategoryTheory.BasedCategory.RestrictInclusion

namespace CategoryTheory.CofiberedCategoryOver.Groupoids

open BasedCategory StronglyCocartesianLift

variable
  (G : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) v, max u v}
    (CompleteLocalAlgCat Λ k))

/-- Chosen pushforward of `ξ` to the included `n`th truncation of its complete local base,
packaged as a restricted object. -/
def completionUnitStage (ξ : G.total) (n : ℕ) :
    BasedCategory.RestrictInclusion G.toBasedCategory :=
  let l := ofCleavage (cleavageOp G.p)
    (FormalObject.truncationToInclusion (G.p.obj ξ) n)
  BasedCategory.RestrictInclusion.of l.target ((G.p.obj ξ).truncation n) l.targetObj

/-- The Artinian base of a unit stage is the corresponding truncation. -/
theorem completionUnitStage_base (ξ : G.total) (n : ℕ) :
    (completionUnitStage G ξ n).base = (G.p.obj ξ).truncation n := sorry

/-- Induced successor map between chosen truncation pushforwards. -/
def completionUnitStep (ξ : G.total) (n : ℕ) :
    completionUnitStage G ξ (n + 1) ⟶ completionUnitStage G ξ n :=
  let lsucc := ofCleavage (cleavageOp G.p)
    (FormalObject.truncationToInclusion (G.p.obj ξ) (n + 1))
  let l := ofCleavage (cleavageOp G.p)
    (FormalObject.truncationToInclusion (G.p.obj ξ) n)
  { obj :=
      @IsStronglyCocartesian.map _ _ _ _ G.p _ _ _ _
        (FormalObject.truncationToInclusion (G.p.obj ξ) (n + 1)) lsucc.hom
        lsucc.isStronglyCocartesian _ _
        (inclusion.map ((G.p.obj ξ).truncationMap n))
        (FormalObject.truncationToInclusion (G.p.obj ξ) n) sorry l.hom l.isHomLift
    base := (G.p.obj ξ).truncationMap n
    over := sorry }

/-- Stage map of the unit induced by a morphism of `G`. -/
def completionUnitMapStage {ξ η : G.total} (a : ξ ⟶ η) (n : ℕ) :
    completionUnitStage G ξ n ⟶ completionUnitStage G η n :=
  let lξ := ofCleavage (cleavageOp G.p)
    (FormalObject.truncationToInclusion (G.p.obj ξ) n)
  let lη := ofCleavage (cleavageOp G.p)
    (FormalObject.truncationToInclusion (G.p.obj η) n)
  { obj :=
      @IsStronglyCocartesian.map _ _ _ _ G.p _ _ _ _
        (FormalObject.truncationToInclusion (G.p.obj ξ) n) lξ.hom
        lξ.isStronglyCocartesian _ _
        (inclusion.map (truncationHom (G.p.map a) n))
        (G.p.map a ≫ FormalObject.truncationToInclusion (G.p.obj η) n) sorry
        (a ≫ lη.hom) sorry
    base := truncationHom (G.p.map a) n
    over := sorry }

/-- The unit `G ⟶ hat(G|_{C_Λ})` sending `ξ` over `R` to the formal object of chosen
pushforwards `(R, ξ_n, f_n)`. -/
def completionUnit :
    G.toBasedCategory ⥤ᵇ
      BasedCategory.ofFunctor
        (completion (BasedCategory.RestrictInclusion.projectionTotal G.toBasedCategory)) where
  toFunctor :=
    { obj ξ :=
        FormalObject.of (G.p.obj ξ)
          (fun n ↦ ULiftHom.objUp (completionUnitStage G ξ n))
          (fun n ↦
            (ULiftHom.up : BasedCategory.RestrictInclusion G.toBasedCategory ⥤
                BasedCategory.RestrictInclusion.total G.toBasedCategory).map
              (completionUnitStep G ξ n))
          (fun n ↦ rfl) (fun n ↦ sorry)
      map a :=
        { base := G.p.map a
          app := fun n ↦
            (ULiftHom.up : BasedCategory.RestrictInclusion G.toBasedCategory ⥤
                BasedCategory.RestrictInclusion.total G.toBasedCategory).map
              (completionUnitMapStage G a n)
          baseTrunc := fun n ↦ truncationHom (G.p.map a) n
          over := sorry
          baseTrunc_spec := sorry
          naturality := sorry }
      map_id := sorry
      map_comp := sorry }
  w := sorry

/-- The unit sends an object over `R` to a formal object with complete local base `R`. -/
theorem completionUnit_obj_base (ξ : G.total) :
    ((completionUnit G).obj ξ).base = G.p.obj ξ := sorry

/-- The unit sends `ξ` over `R` to the inverse system of chosen pushforwards to
`R.truncation n`. -/
theorem completionUnit_obj_family (ξ : G.total) (n : ℕ) :
    let ζ := ULiftHom.objDown ((completionUnit G).obj ξ).system.family n
    ζ.base = (G.p.obj ξ).truncation n ∧
      G.p.obj ζ.obj = toComplete ((G.p.obj ξ).truncation n) := sorry

/-- The unit lies over the identity of `Ĉ_Λ`. -/
theorem completionUnit_w :
    (completionUnit G).toFunctor ⋙
        completion (BasedCategory.RestrictInclusion.projectionTotal G.toBasedCategory) =
      G.p := sorry

variable
  (F : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k))

/-- Bundled completion of a category cofibered in groupoids over `C_Λ`. -/
def completionGroupoids :
    CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) v, max u v}
      (CompleteLocalAlgCat Λ k) :=
  ofFunctor (completion F.p)

/-- The counit `hat F |_{C_Λ} ⟶ F`, as the comparison with `FormalObject.Restrict`
followed by `can`. -/
def completionCounit :
    (restrictInclusion (completionGroupoids F)).toBasedCategory ⥤ᵇ F.toBasedCategory where
  toFunctor := BasedCategory.RestrictInclusion.toFormalRestrictFunctor ⋙ FormalObject.can F.p
  w := sorry

/-- The counit is the evaluation functor `can` of Remark 90.7.7 after the comparison
`RestrictInclusion ≃ FormalObject.Restrict`. -/
theorem completionCounit_eq_basedCan :
    (completionCounit F).toFunctor =
      BasedCategory.RestrictInclusion.toFormalRestrictFunctor ⋙ FormalObject.can F.p := sorry

end CategoryTheory.CofiberedCategoryOver.Groupoids

end
