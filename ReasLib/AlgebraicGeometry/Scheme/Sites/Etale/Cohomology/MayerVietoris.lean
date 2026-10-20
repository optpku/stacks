/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import ReasLib.CategoryTheory.ComposableArrows.ZeroPrecomp
public import ReasLib.CategoryTheory.Sites.Cohomology.Map

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace EtaleMayerVietoris

/-- The inclusion of the intersection into the first open is a morphism over `X`. -/
theorem intersectionToLeft_over (X : Scheme.{u}) (U V : X.Opens) :
    X.homOfLE inf_le_left ≫ U.ι = (U ⊓ V).ι := sorry

/-- The morphism from the intersection open to the first open in the small etale site. -/
abbrev intersectionToLeft (X : Scheme.{u}) (U V : X.Opens) :
    Scheme.Etale.mk (U ⊓ V).ι ⟶ Scheme.Etale.mk U.ι :=
  MorphismProperty.Over.homMk (X.homOfLE inf_le_left) (intersectionToLeft_over X U V)

/-- The inclusion of the intersection into the second open is a morphism over `X`. -/
theorem intersectionToRight_over (X : Scheme.{u}) (U V : X.Opens) :
    X.homOfLE inf_le_right ≫ V.ι = (U ⊓ V).ι := sorry

/-- The morphism from the intersection open to the second open in the small etale site. -/
abbrev intersectionToRight (X : Scheme.{u}) (U V : X.Opens) :
    Scheme.Etale.mk (U ⊓ V).ι ⟶ Scheme.Etale.mk V.ι :=
  MorphismProperty.Over.homMk (X.homOfLE inf_le_right) (intersectionToRight_over X U V)

/-- The morphism from the first open to `X` in the small etale site. -/
abbrev leftToSpace (X : Scheme.{u}) (U : X.Opens) :
    Scheme.Etale.mk U.ι ⟶ Scheme.Etale.mk (𝟙 X) :=
  MorphismProperty.Over.homMk U.ι

/-- The morphism from the second open to `X` in the small etale site. -/
abbrev rightToSpace (X : Scheme.{u}) (V : X.Opens) :
    Scheme.Etale.mk V.ι ⟶ Scheme.Etale.mk (𝟙 X) :=
  MorphismProperty.Over.homMk V.ι

/-- An open inclusion into `X` is a monomorphism in the small etale site. -/
instance openToSpace_mono (X : Scheme.{u}) (U : X.Opens) : Mono (leftToSpace X U) := sorry

/-- The two composites from the intersection open to `X` agree. -/
theorem openSquare_fac (X : Scheme.{u}) (U V : X.Opens) :
    intersectionToLeft X U V ≫ leftToSpace X U =
      intersectionToRight X U V ≫ rightToSpace X V := sorry

/-- The commutative square of small-etale objects determined by two opens. -/
def openSquare (X : Scheme.{u}) (U V : X.Opens) : Square X.Etale where
  X₁ := Scheme.Etale.mk (U ⊓ V).ι
  X₂ := Scheme.Etale.mk U.ι
  X₃ := Scheme.Etale.mk V.ι
  X₄ := Scheme.Etale.mk (𝟙 X)
  f₁₂ := intersectionToLeft X U V
  f₁₃ := intersectionToRight X U V
  f₂₄ := leftToSpace X U
  f₃₄ := rightToSpace X V
  fac := openSquare_fac X U V

/-- The first open-to-space arrow of the open square is a monomorphism. -/
theorem openSquare_mono_f₂₄ (X : Scheme.{u}) (U V : X.Opens) :
    Mono (openSquare X U V).f₂₄ := sorry

/-- The second open-to-space arrow of the open square is a monomorphism. -/
theorem openSquare_mono_f₃₄ (X : Scheme.{u}) (U V : X.Opens) :
    Mono (openSquare X U V).f₃₄ := sorry

/-- The open-intersection square is a pullback square in the small etale site. -/
theorem openSquare_isPullback (X : Scheme.{u}) (U V : X.Opens) :
    (openSquare X U V).IsPullback := sorry

/-- If `U` and `V` cover `X`, their two maps cover the terminal small-etale object. -/
theorem openSquare_mem_smallEtaleTopology (X : Scheme.{u}) (U V : X.Opens)
    (hUV : U ⊔ V = ⊤) :
    Sieve.ofTwoArrows (openSquare X U V).f₂₄ (openSquare X U V).f₃₄ ∈
      X.smallEtaleTopology (openSquare X U V).X₄ := sorry

/-- The canonical Mayer-Vietoris square in the small etale site attached to `X = U ∪ V`. -/
noncomputable def square (X : Scheme.{u}) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    [HasWeakSheafify X.smallEtaleTopology (Type u)] :
    X.smallEtaleTopology.MayerVietorisSquare :=
  @GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback _ _ _ _
    (openSquare X U V) (openSquare_mono_f₂₄ X U V) (openSquare_mono_f₃₄ X U V)
    (openSquare_isPullback X U V) (openSquare_mem_smallEtaleTopology X U V hUV)

/-- The intersection object of the canonical small-etale Mayer-Vietoris square. -/
theorem square_X₁ (X : Scheme.{u}) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    [HasWeakSheafify X.smallEtaleTopology (Type u)] :
    (square X U V hUV).X₁ = Scheme.Etale.mk (U ⊓ V).ι := sorry

/-- The first open object of the canonical small-etale Mayer-Vietoris square. -/
theorem square_X₂ (X : Scheme.{u}) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    [HasWeakSheafify X.smallEtaleTopology (Type u)] :
    (square X U V hUV).X₂ = Scheme.Etale.mk U.ι := sorry

/-- The second open object of the canonical small-etale Mayer-Vietoris square. -/
theorem square_X₃ (X : Scheme.{u}) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    [HasWeakSheafify X.smallEtaleTopology (Type u)] :
    (square X U V hUV).X₃ = Scheme.Etale.mk V.ι := sorry

/-- The ambient object of the canonical small-etale Mayer-Vietoris square. -/
theorem square_X₄ (X : Scheme.{u}) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    [HasWeakSheafify X.smallEtaleTopology (Type u)] :
    (square X U V hUV).X₄ = Scheme.Etale.mk (𝟙 X) := sorry

variable {X : Scheme.{u}}
variable [HasWeakSheafify X.smallEtaleTopology (Type u)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]

/-- The cohomology map at a small-etale object induced by a coefficient-sheaf morphism. -/
noncomputable abbrev mapAt {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (φ : F ⟶ G) (n : ℕ) (W : X.Etale) : F.H' n W ⟶ G.H' n W :=
  Sheaf.cohomologyMap φ n W

/-- The biproduct of the cohomology maps at the two middle objects of a square. -/
noncomputable abbrev mapBiprod
    (S : X.smallEtaleTopology.MayerVietorisSquare)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (φ : F ⟶ G) (n : ℕ) :
    F.H' n S.X₂ ⊞ F.H' n S.X₃ ⟶ G.H' n S.X₂ ⊞ G.H' n S.X₃ :=
  biprod.map (mapAt φ n S.X₂) (mapAt φ n S.X₃)

/-- Naturality of the first arrow in a small-etale Mayer-Vietoris segment. -/
theorem map_naturality_zero
    (S : X.smallEtaleTopology.MayerVietorisSquare)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ) :
    (S.sequence F n (n + 1) rfl).map' 0 1 ≫ mapBiprod S φ n =
      mapAt φ n S.X₄ ≫ (S.sequence G n (n + 1) rfl).map' 0 1 := sorry

/-- Naturality of the second arrow in a small-etale Mayer-Vietoris segment. -/
theorem map_naturality_one
    (S : X.smallEtaleTopology.MayerVietorisSquare)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ) :
    (S.sequence F n (n + 1) rfl).map' 1 2 ≫ mapAt φ n S.X₁ =
      mapBiprod S φ n ≫ (S.sequence G n (n + 1) rfl).map' 1 2 := sorry

/-- Naturality of the connecting arrow in a small-etale Mayer-Vietoris segment. -/
theorem map_naturality_two
    (S : X.smallEtaleTopology.MayerVietorisSquare)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ) :
    (S.sequence F n (n + 1) rfl).map' 2 3 ≫ mapAt φ (n + 1) S.X₄ =
      mapAt φ n S.X₁ ≫ (S.sequence G n (n + 1) rfl).map' 2 3 := sorry

/-- Naturality of the fourth arrow in a small-etale Mayer-Vietoris segment. -/
theorem map_naturality_three
    (S : X.smallEtaleTopology.MayerVietorisSquare)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ) :
    (S.sequence F n (n + 1) rfl).map' 3 4 ≫ mapBiprod S φ (n + 1) =
      mapAt φ (n + 1) S.X₄ ≫ (S.sequence G n (n + 1) rfl).map' 3 4 := sorry

/-- Naturality of the fifth arrow in a small-etale Mayer-Vietoris segment. -/
theorem map_naturality_four
    (S : X.smallEtaleTopology.MayerVietorisSquare)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ) :
    (S.sequence F n (n + 1) rfl).map' 4 5 ≫ mapAt φ (n + 1) S.X₁ =
      mapBiprod S φ (n + 1) ≫ (S.sequence G n (n + 1) rfl).map' 4 5 := sorry

/-- The canonical morphism of Mayer-Vietoris segments induced by a sheaf morphism. -/
noncomputable def sequenceMap
    (S : X.smallEtaleTopology.MayerVietorisSquare)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ) :
    S.sequence F n (n + 1) rfl ⟶ S.sequence G n (n + 1) rfl :=
  ComposableArrows.homMk₅
    (mapAt φ n S.X₄) (mapBiprod S φ n) (mapAt φ n S.X₁)
    (mapAt φ (n + 1) S.X₄) (mapBiprod S φ (n + 1)) (mapAt φ (n + 1) S.X₁)
    (map_naturality_zero S φ n) (map_naturality_one S φ n)
    (map_naturality_two S φ n) (map_naturality_three S φ n)
    (map_naturality_four S φ n)

/-- The canonical segment map induced by an identity sheaf morphism is the identity. -/
theorem sequenceMap_id (S : X.smallEtaleTopology.MayerVietorisSquare)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    sequenceMap S (𝟙 F) n = 𝟙 _ := sorry

/-- Canonical Mayer-Vietoris segment maps respect composition of sheaf morphisms. -/
theorem sequenceMap_comp (S : X.smallEtaleTopology.MayerVietorisSquare)
    {F G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (φ : F ⟶ G) (ψ : G ⟶ H) (n : ℕ) :
    sequenceMap S (φ ≫ ψ) n = sequenceMap S φ n ≫ sequenceMap S ψ n := sorry

/-- A Mayer-Vietoris segment as a functor of its coefficient sheaf. -/
noncomputable def sequenceFunctor (S : X.smallEtaleTopology.MayerVietorisSquare) (n : ℕ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      ComposableArrows AddCommGrpCat.{u} 5 where
  obj F := S.sequence F n (n + 1) rfl
  map φ := sequenceMap S φ n
  map_id F := sequenceMap_id S F n
  map_comp φ ψ := sequenceMap_comp S φ ψ n

/-- The object action of the Mayer-Vietoris sequence functor is the canonical segment. -/
theorem sequenceFunctor_obj (S : X.smallEtaleTopology.MayerVietorisSquare) (n : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (sequenceFunctor S n).obj F = S.sequence F n (n + 1) rfl := sorry

/-- The morphism action of the Mayer-Vietoris sequence functor is the canonical segment map. -/
theorem sequenceFunctor_map (S : X.smallEtaleTopology.MayerVietorisSquare) (n : ℕ)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) :
    (sequenceFunctor S n).map φ = sequenceMap S φ n := sorry

/-- Exactness of the augmented and degreewise Mayer--Vietoris cohomology segments for a two-open cover. -/
@[stacks 0A50]
theorem mayerVietorisEtaleExact (X : Scheme.{u}) (U V : X.Opens)
    (hUV : U ⊔ V = ⊤)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u},
      (((square X U V hUV).sequence F 0 1 rfl).zeroPrecomp 1).Exact ∧
        ∀ n : ℕ,
          ((square X U V hUV).sequence F n (n + 1) rfl).Exact := sorry

/-- Functoriality of the Mayer--Vietoris cohomology segments in the coefficient sheaf. -/
@[stacks 0A50]
theorem mayerVietorisEtaleFunctorial (X : Scheme.{u}) (U V : X.Opens)
    (hUV : U ⊔ V = ⊤)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (n : ℕ) {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) :
    (sequenceFunctor (square X U V hUV) n).obj F =
        (square X U V hUV).sequence F n (n + 1) rfl ∧
      (sequenceFunctor (square X U V hUV) n).map φ =
        sequenceMap (square X U V hUV) φ n := sorry

end EtaleMayerVietoris
