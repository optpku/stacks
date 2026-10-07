module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.Data.Countable.Small
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import stacks_project.Chap90.Definition_90_7_3_CompleteLocal

/-!
# Set-valued completion of a functor on `C_Λ`

The completion of `F : ArtinianLocalAlgCat Λ k ⥤ Type w` is the functor
`typesCompletion F : CompleteLocalAlgCat Λ k ⥤ Type w` sending a complete
local algebra `S` to the inverse limit of `F` on the maximal-adic truncations
of `S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- The sequential inverse system of maximal-adic truncations of a complete local
algebra, with successor transitions `truncationMap`. -/
noncomputable def truncationSystem (S : CompleteLocalAlgCat Λ k) :
    SequentialInverseSystem (ArtinianLocalAlgCat Λ k) :=
  Functor.ofOpSequence (fun n ↦ S.truncationMap n)

/-- Stage `n` of the truncation tower is the `n`th maximal-adic truncation. -/
theorem truncationSystem_obj (S : CompleteLocalAlgCat Λ k) (n : ℕ) :
    S.truncationSystem.obj (op n) = S.truncation n := sorry

/-- The successor transition of the truncation tower is the canonical truncation
projection. -/
theorem truncationSystem_stepMap (S : CompleteLocalAlgCat Λ k) (n : ℕ) :
    S.truncationSystem.stepMap n = S.truncationMap n := sorry

/-- A local algebra map sends a power of the source maximal ideal into the
corresponding power of the target maximal ideal. -/
theorem truncationHom_le {S T : CompleteLocalAlgCat Λ k} (f : S ⟶ T) (n : ℕ) :
    maximalIdeal S.carrier ^ (n + 1) ≤
      (maximalIdeal T.carrier ^ (n + 1)).comap f.hom := sorry

/-- The morphism of truncations induced by a morphism of complete local algebras. -/
noncomputable def truncationHom {S T : CompleteLocalAlgCat Λ k} (f : S ⟶ T) (n : ℕ) :
    S.truncation n ⟶ T.truncation n where
  hom := Ideal.quotientMapₐ (maximalIdeal T.carrier ^ (n + 1)) f.hom (truncationHom_le f n)
  isLocalHom := sorry
  residue_compat := sorry

/-- The induced truncation map is the quotient of the underlying algebra map. -/
theorem truncationHom_spec {S T : CompleteLocalAlgCat Λ k} (f : S ⟶ T) (n : ℕ) :
    (truncationHom f n).hom.comp
        (Ideal.Quotient.mkₐ Λ (maximalIdeal S.carrier ^ (n + 1))) =
      (Ideal.Quotient.mkₐ Λ (maximalIdeal T.carrier ^ (n + 1))).comp f.hom := sorry

/-- Successive truncations of a complete local morphism intertwine the truncation
projections. -/
theorem truncationSystemMap_naturality {S T : CompleteLocalAlgCat Λ k} (f : S ⟶ T)
    (n : ℕ) :
    S.truncationSystem.map (homOfLE (n.le_add_right 1)).op ≫ truncationHom f n =
      truncationHom f (n + 1) ≫
        T.truncationSystem.map (homOfLE (n.le_add_right 1)).op := sorry

/-- The natural transformation of truncation towers induced by a morphism of complete
local algebras. -/
noncomputable def truncationSystemMap {S T : CompleteLocalAlgCat Λ k} (f : S ⟶ T) :
    S.truncationSystem ⟶ T.truncationSystem :=
  NatTrans.ofOpSequence (fun n ↦ truncationHom f n) (truncationSystemMap_naturality f)

/-- The component of `truncationSystemMap f` at stage `n` is `truncationHom f n`. -/
theorem truncationSystemMap_app {S T : CompleteLocalAlgCat Λ k} (f : S ⟶ T) (n : ℕ) :
    (truncationSystemMap f).app (op n) = truncationHom f n := sorry

end CompleteLocalAlgCat

namespace CategoryTheory.Functor

/-- The set-valued completion of `F : ArtinianLocalAlgCat Λ k ⥤ Type w`, sending a
complete local algebra `S` to the inverse limit of `F` on the truncations of `S`. -/
noncomputable def typesCompletion (F : ArtinianLocalAlgCat Λ k ⥤ Type w) :
    CompleteLocalAlgCat Λ k ⥤ Type w where
  obj S := limit (S.truncationSystem ⋙ F)
  map f := limMap (whiskerRight (CompleteLocalAlgCat.truncationSystemMap f) F)
  map_id := sorry
  map_comp := sorry

/-- The value of the set-valued completion at `S` is the inverse limit of `F` on the
truncation tower of `S`. -/
theorem typesCompletion_obj (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (S : CompleteLocalAlgCat Λ k) :
    (typesCompletion F).obj S = limit (S.truncationSystem ⋙ F) := sorry

/-- The set-valued completion acts on morphisms by the induced map of inverse
limits. -/
theorem typesCompletion_map (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    {S T : CompleteLocalAlgCat Λ k} (f : S ⟶ T) :
    (typesCompletion F).map f =
      limMap (whiskerRight (CompleteLocalAlgCat.truncationSystemMap f) F) := sorry

/-- The value of the set-valued completion is the type of compatible sections of `F`
on the truncation tower. -/
noncomputable def typesCompletion_obj_equiv (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (S : CompleteLocalAlgCat Λ k) :
    (typesCompletion F).obj S ≃ (S.truncationSystem ⋙ F).sections :=
  Types.limitEquivSections (S.truncationSystem ⋙ F)

/-- The sections equivalence evaluates a completion point at a truncation stage by
the corresponding limit projection. -/
theorem typesCompletion_obj_equiv_apply (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (S : CompleteLocalAlgCat Λ k) (x : (typesCompletion F).obj S)
    (j : ℕᵒᵖ) :
    (typesCompletion_obj_equiv F S x).val j =
      limit.π (S.truncationSystem ⋙ F) j x := sorry

/-- The opposite of the category-of-elements projection of a set-valued functor on
`C_Λ` is fibered in groupoids. -/
instance pi_op_isFiberedInGroupoids (F : ArtinianLocalAlgCat Λ k ⥤ Type w) :
    IsFibered.InGroupoids (CategoryOfElements.π F).op := sorry

/-- The element of `F` at the `n`th truncation of `S` determined by a completion
point. -/
noncomputable def typesCompletionStage (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (S : CompleteLocalAlgCat Λ k) (x : (typesCompletion F).obj S) (n : ℕ) :
    F.Elements :=
  ⟨S.truncation n, limit.π (S.truncationSystem ⋙ F) (op n) x⟩

/-- A completion stage lies over the corresponding truncation of `S`. -/
theorem typesCompletionStage_over_obj (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (S : CompleteLocalAlgCat Λ k) (x : (typesCompletion F).obj S) (n : ℕ) :
    (CategoryOfElements.π F).obj (typesCompletionStage F S x n) = S.truncation n := sorry

/-- The inverse system of elements of `F` over the truncations of `S` determined by
a point of the set-valued completion. -/
noncomputable def typesCompletionSystem (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (S : CompleteLocalAlgCat Λ k) (x : (typesCompletion F).obj S) :
    SequentialInverseSystem F.Elements :=
  Functor.ofOpSequence (fun n ↦
    CategoryOfElements.homMk (typesCompletionStage F S x (n + 1))
      (typesCompletionStage F S x n) (S.truncationMap n) sorry)

/-- Stage `n` of the extracted inverse system is the element of `F` at the `n`th
truncation given by the corresponding limit projection. -/
theorem typesCompletionSystem_family (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (S : CompleteLocalAlgCat Λ k) (x : (typesCompletion F).obj S) (n : ℕ) :
    (typesCompletionSystem F S x).family n = typesCompletionStage F S x n := sorry

/-- Each stage of the extracted inverse system lies over the corresponding
truncation of `S`. -/
theorem typesCompletionSystem_over_obj (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (S : CompleteLocalAlgCat Λ k) (x : (typesCompletion F).obj S) (n : ℕ) :
    (CategoryOfElements.π F).obj ((typesCompletionSystem F S x).family n) =
      S.truncation n := sorry

/-- Successor transitions of the extracted inverse system lie over the truncation
projections of `S`. -/
instance typesCompletionSystem_over_step (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (S : CompleteLocalAlgCat Λ k) (x : (typesCompletion F).obj S) (n : ℕ) :
    (CategoryOfElements.π F).IsHomLift (S.truncationMap n)
      ((typesCompletionSystem F S x).stepMap n) := sorry

/-- The stage-`n` element of a compatible tower, transported along
`IsHomLift.codomain_eq` at zero and `IsHomLift.domain_eq` at successors. -/
noncomputable def typesCompletionOfSystemStage (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (S : CompleteLocalAlgCat Λ k) (ξ : SequentialInverseSystem F.Elements)
    (over_step : ∀ n, (CategoryOfElements.π F).IsHomLift (S.truncationMap n) (ξ.stepMap n))
    (n : ℕ) : F.obj (S.truncation n) :=
  n.casesOn
    (F.map (eqToHom
        (@IsHomLift.codomain_eq _ _ _ _ (CategoryOfElements.π F) _ _ _ _
          (S.truncationMap 0) (ξ.stepMap 0) (over_step 0)))
      (ξ.family 0).snd)
    (fun n ↦ F.map (eqToHom
        (@IsHomLift.domain_eq _ _ _ _ (CategoryOfElements.π F) _ _ _ _
          (S.truncationMap n) (ξ.stepMap n) (over_step n)))
      (ξ.family (n + 1)).snd)

/-- Reconstruct a completion value from an inverse system of elements of `F` whose
successor transitions lie over the truncation projections of `S`. -/
noncomputable def typesCompletionOfSystem (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (S : CompleteLocalAlgCat Λ k) (ξ : SequentialInverseSystem F.Elements)
    (over_step : ∀ n, (CategoryOfElements.π F).IsHomLift (S.truncationMap n) (ξ.stepMap n)) :
    (typesCompletion F).obj S :=
  Types.Limit.mk (S.truncationSystem ⋙ F)
    (fun j ↦ typesCompletionOfSystemStage F S ξ over_step j.unop) sorry

/-- The reconstructed completion point projects to the transported stage element. -/
theorem typesCompletionOfSystem_apply (F : ArtinianLocalAlgCat Λ k ⥤ Type w)
    (S : CompleteLocalAlgCat Λ k) (ξ : SequentialInverseSystem F.Elements)
    (over_step : ∀ n, (CategoryOfElements.π F).IsHomLift (S.truncationMap n) (ξ.stepMap n))
    (j : ℕᵒᵖ) :
    limit.π (S.truncationSystem ⋙ F) j (typesCompletionOfSystem F S ξ over_step) =
      typesCompletionOfSystemStage F S ξ over_step j.unop := sorry

/-- Extracting the inverse system of elements and returning to the inverse limit
recovers the original completion point. -/
theorem typesCompletionOfSystem_typesCompletionSystem
    (F : ArtinianLocalAlgCat Λ k ⥤ Type w) (S : CompleteLocalAlgCat Λ k)
    (x : (typesCompletion F).obj S) :
    typesCompletionOfSystem F S (typesCompletionSystem F S x)
      (typesCompletionSystem_over_step F S x) = x := sorry

/-- The inverse system of elements of a compatible tower is recovered from its
inverse-limit completion value. -/
theorem typesCompletionSystem_typesCompletionOfSystem
    (F : ArtinianLocalAlgCat Λ k ⥤ Type w) (S : CompleteLocalAlgCat Λ k)
    (ξ : SequentialInverseSystem F.Elements)
    (over_step : ∀ n, (CategoryOfElements.π F).IsHomLift (S.truncationMap n) (ξ.stepMap n)) :
    typesCompletionSystem F S (typesCompletionOfSystem F S ξ over_step) = ξ := sorry

end CategoryTheory.Functor
