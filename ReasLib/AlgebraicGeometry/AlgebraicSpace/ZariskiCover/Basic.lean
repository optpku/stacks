/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion

/-!
# Zariski coverings of algebraic spaces

A Zariski covering of an algebraic space is a small family of open immersions whose
induced map from the coproduct of functors of points is locally surjective as fppf sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism of functors of points `∐ X i ⟶ F` induced by a family of morphisms of
algebraic spaces, whose local surjectivity expresses surjectivity after sheafification. -/
def sheafCoproductDesc {S : Scheme.{u}} {I : Type v} [small : Small.{u} I] {F : AlgebraicSpace S}
    (X : I → AlgebraicSpace S) (f : ∀ i, X i ⟶ F) :
    (∐ fun i ↦ (X i).functorOfPoints) ⟶ F.functorOfPoints :=
  Sigma.desc fun i ↦ f i

/-- A Zariski covering of an algebraic space `F` is a small indexed family of open immersions
into `F` such that the induced map from the coproduct of the open subspaces is a surjective map
of fppf sheaves. -/
structure ZariskiCover {S : Scheme.{u}} (F : AlgebraicSpace S) where
  /-- The index type of the covering. -/
  I₀ : Type v
  /-- The open subspaces of `F`. -/
  X : I₀ → AlgebraicSpace S
  /-- The inclusion of each open subspace. -/
  f : ∀ i, X i ⟶ F
  /-- Each inclusion is an open immersion of algebraic spaces. -/
  isOpenImmersion : ∀ i, IsOpenImmersion (f i)
  /-- The index type is small relative to the universe of schemes over `S`. -/
  small : Small.{u} I₀
  /-- The coproduct of the open subspaces maps surjectively onto `F` as fppf sheaves. -/
  covers : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
    (sheafCoproductDesc (small := small) X f)

namespace ZariskiCover

/-- Build a Zariski covering from a small family of open immersions whose coproduct map is
locally surjective as fppf sheaves. -/
def ofCovers {S : Scheme.{u}} {F : AlgebraicSpace S} {I : Type v} [Small.{u} I]
    (X : I → AlgebraicSpace S) (f : ∀ i, X i ⟶ F)
    (h_open : ∀ i, IsOpenImmersion (f i))
    (h_covers : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (sheafCoproductDesc (small := inferInstance) X f)) :
    ZariskiCover F where
  I₀ := I
  X := X
  f := f
  isOpenImmersion := h_open
  small := inferInstance
  covers := h_covers

/-- The index type of `ofCovers X f h_open h_covers` is `I`. -/
@[simp]
theorem ofCovers_I₀ {S : Scheme.{u}} {F : AlgebraicSpace S} {I : Type v} [Small.{u} I]
    (X : I → AlgebraicSpace S) (f : ∀ i, X i ⟶ F)
    (h_open : ∀ i, IsOpenImmersion (f i))
    (h_covers : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (sheafCoproductDesc (small := inferInstance) X f)) :
    (ofCovers X f h_open h_covers).I₀ = I := sorry

/-- The component morphisms of `ofCovers X f h_open h_covers` are the given family `f`. -/
@[simp]
theorem ofCovers_f {S : Scheme.{u}} {F : AlgebraicSpace S} {I : Type v} [Small.{u} I]
    (X : I → AlgebraicSpace S) (f : ∀ i, X i ⟶ F)
    (h_open : ∀ i, IsOpenImmersion (f i))
    (h_covers : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (sheafCoproductDesc (small := inferInstance) X f)) :
    (ofCovers X f h_open h_covers).f = f := sorry

/-- The sheaf morphism `∐ 𝒰.X i ⟶ F` associated to a Zariski covering. -/
def coverSheafHom {S : Scheme.{u}} {F : AlgebraicSpace S} (𝒰 : ZariskiCover F) :=
  sheafCoproductDesc (small := 𝒰.small) 𝒰.X 𝒰.f

/-- `coverSheafHom 𝒰` is the coproduct descent of the component inclusions. -/
theorem coverSheafHom_eq {S : Scheme.{u}} {F : AlgebraicSpace S} (𝒰 : ZariskiCover F) :
    𝒰.coverSheafHom = sheafCoproductDesc (small := 𝒰.small) 𝒰.X 𝒰.f := sorry

/-- A Zariski covering consists of open immersions whose coproduct map is locally surjective
as fppf sheaves. -/
theorem spec {S : Scheme.{u}} {F : AlgebraicSpace S} (𝒰 : ZariskiCover F) :
    (∀ i, IsOpenImmersion (𝒰.f i)) ∧
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) 𝒰.coverSheafHom := sorry

/-- The identity Zariski covering of an algebraic space, with a single open subspace `F ⊂ F`. -/
def id {S : Scheme.{u}} (F : AlgebraicSpace S) : ZariskiCover.{u} F where
  I₀ := PUnit.{u + 1}
  X := fun _ ↦ F
  f := fun _ ↦ 𝟙 F
  isOpenImmersion := fun _ ↦ inferInstance
  small := inferInstance
  covers := sorry

/-- The unique component of the identity Zariski covering is the identity morphism. -/
@[simp]
theorem id_f {S : Scheme.{u}} (F : AlgebraicSpace S) (i : PUnit.{u + 1}) :
    (id F).f i = 𝟙 F := sorry

/-- Pulling a Zariski covering of `F` back along a morphism `T ⟶ F` from a scheme yields a
Zariski open cover of `T`. -/
def pullbackOpenCover {S : Scheme.{u}} {F : AlgebraicSpace S} (𝒰 : ZariskiCover F)
    {T : Over S} (a : yoneda.obj T ⟶ F.functorOfPoints) :
    Scheme.OpenCover T.left :=
  Scheme.Cover.mkOfCovers 𝒰.I₀
    (fun i ↦ ((𝒰.isOpenImmersion i).presheaf.rep.pullback a).left)
    (fun i ↦ ((𝒰.isOpenImmersion i).presheaf.rep.snd a).left) sorry
    (fun i ↦ (𝒰.isOpenImmersion i).presheaf.property_snd a)

/-- The `i`-th scheme in `pullbackOpenCover 𝒰 a` is the represented pullback of `𝒰.f i`
along `a`. -/
theorem pullbackOpenCover_X {S : Scheme.{u}} {F : AlgebraicSpace S} (𝒰 : ZariskiCover F)
    {T : Over S} (a : yoneda.obj T ⟶ F.functorOfPoints) (i : 𝒰.I₀) :
    (𝒰.pullbackOpenCover a).X i = ((𝒰.isOpenImmersion i).presheaf.rep.pullback a).left := sorry

/-- The `i`-th map of `pullbackOpenCover 𝒰 a` is the represented pullback projection of
`𝒰.f i` along `a`. -/
theorem pullbackOpenCover_f {S : Scheme.{u}} {F : AlgebraicSpace S} (𝒰 : ZariskiCover F)
    {T : Over S} (a : yoneda.obj T ⟶ F.functorOfPoints) (i : 𝒰.I₀) :
    (𝒰.pullbackOpenCover a).f i = ((𝒰.isOpenImmersion i).presheaf.rep.snd a).left := sorry

/-- Each inclusion of a Zariski covering is a monomorphism, corresponding to the subspace
reading `X i ⊂ F`. -/
theorem mono {S : Scheme.{u}} {F : AlgebraicSpace S} (𝒰 : ZariskiCover F) (i : 𝒰.I₀) :
    Mono (𝒰.f i) := sorry

end ZariskiCover

end AlgebraicGeometry.AlgebraicSpace
