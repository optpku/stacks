module

public import stacks_project.Chap07.Definition_7_7_1_Sheaf

@[expose] public section

open CategoryTheory CategoryTheory.Limits Equalizer.Presieve

/-- Definition 7.7.1: a Type-valued presheaf `P` on a site `J` is a sheaf if for
every covering family `{Uᵢ ⟶ U}_{i ∈ I}` in `J` the restriction map
`P.obj (op B) ⟶ Arrows.FirstObj P X` is the equalizer of `Arrows.firstMap`
(`pr₀*`) and `Arrows.secondMap` (`pr₁*`) into `Arrows.SecondObj P X π`. -/
@[stacks 00VM]
abbrev IsSheafOfTypes.{u, v} {C : Type u} [Category.{v} C]
    (J : Precoverage C) [J.IsSite] (P : Cᵒᵖ ⥤ Type (max u v)) : Prop :=
  Precoverage.IsSheafOfTypes.{u, v} J P

/-- The sheaf-of-types predicate is the equalizer condition on every chosen
covering family. -/
theorem isSheafOfTypes_iff.{u, v} {C : Type u} [Category.{v} C]
    (J : Precoverage C) [J.IsSite] (P : Cᵒᵖ ⥤ Type (max u v)) :
    IsSheafOfTypes J P ↔
      ∀ {B : C} {I : Type (max u v)}
        (X : I → C) (π : (i : I) → X i ⟶ B)
        [(Presieve.ofArrows X π).HasPairwisePullbacks],
        Presieve.ofArrows X π ∈ J B →
          Nonempty (IsLimit (Fork.ofι (Arrows.forkMap P X π) (Arrows.w P X π))) :=
  sorry
