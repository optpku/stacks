module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import stacks_project.Chap65.Lemma_65_12_4_Immersion

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits MorphismProperty

universe u v

#check (AlgebraicGeometry.AlgebraicSpace.sheafCoproductDesc :
  {S : Scheme.{u}} → {I : Type v} → [small : Small.{u, v} I] → {F : AlgebraicSpace S} →
    (X : I → AlgebraicSpace S) → (f : ∀ i, X i ⟶ F) →
      (∐ fun i ↦ (X i).functorOfPoints) ⟶ F.functorOfPoints)

#check (AlgebraicGeometry.AlgebraicSpace.ZariskiCover.{u, v} :
  {S : Scheme.{u}} → AlgebraicSpace S → Type (max (u + 1) (v + 1)))

#check (AlgebraicGeometry.AlgebraicSpace.ZariskiCover.ofCovers :
  {S : Scheme.{u}} → {F : AlgebraicSpace S} → {I : Type v} → [Small.{u, v} I] →
    (X : I → AlgebraicSpace S) → (f : ∀ i, X i ⟶ F) →
      (h_open : ∀ i, IsOpenImmersion (f i)) →
        (h_covers : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
          (sheafCoproductDesc (small := inferInstance) X f)) → ZariskiCover F)

#check (AlgebraicGeometry.AlgebraicSpace.ZariskiCover.ofCovers_I₀ :
  {S : Scheme.{u}} → {F : AlgebraicSpace S} → {I : Type v} → [Small.{u, v} I] →
    (X : I → AlgebraicSpace S) → (f : ∀ i, X i ⟶ F) →
      (h_open : ∀ i, IsOpenImmersion (f i)) →
        (h_covers : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
          (sheafCoproductDesc (small := inferInstance) X f)) →
            (ZariskiCover.ofCovers X f h_open h_covers).I₀ = I)

#check (AlgebraicGeometry.AlgebraicSpace.ZariskiCover.ofCovers_f :
  {S : Scheme.{u}} → {F : AlgebraicSpace S} → {I : Type v} → [Small.{u, v} I] →
    (X : I → AlgebraicSpace S) → (f : ∀ i, X i ⟶ F) →
      (h_open : ∀ i, IsOpenImmersion (f i)) →
        (h_covers : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
          (sheafCoproductDesc (small := inferInstance) X f)) →
            (ZariskiCover.ofCovers X f h_open h_covers).f = f)

#check (AlgebraicGeometry.AlgebraicSpace.ZariskiCover.coverSheafHom :
  {S : Scheme.{u}} → {F : AlgebraicSpace S} → (𝒰 : ZariskiCover F) →
    (∐ fun i ↦ (𝒰.X i).functorOfPoints) ⟶ F.functorOfPoints)
#check (AlgebraicGeometry.AlgebraicSpace.ZariskiCover.coverSheafHom_eq :
  {S : Scheme.{u}} → {F : AlgebraicSpace S} → (𝒰 : ZariskiCover F) →
    𝒰.coverSheafHom = sheafCoproductDesc (small := 𝒰.small) 𝒰.X 𝒰.f)
#check (AlgebraicGeometry.AlgebraicSpace.ZariskiCover.spec :
  {S : Scheme.{u}} → {F : AlgebraicSpace S} → (𝒰 : ZariskiCover F) →
    (∀ i, IsOpenImmersion (𝒰.f i)) ∧
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) 𝒰.coverSheafHom)
#check (AlgebraicGeometry.AlgebraicSpace.ZariskiCover.id :
  {S : Scheme} → (F : AlgebraicSpace S) → ZariskiCover F)
#check (AlgebraicGeometry.AlgebraicSpace.ZariskiCover.id_f :
  {S : Scheme} → (F : AlgebraicSpace S) → (i : (ZariskiCover.id F).I₀) →
    (ZariskiCover.id F).f i = 𝟙 F)
#check (AlgebraicGeometry.AlgebraicSpace.ZariskiCover.pullbackOpenCover :
  {S : Scheme.{u}} → {F : AlgebraicSpace S} → (𝒰 : ZariskiCover F) →
    {T : Over S} → (yoneda.obj T ⟶ F.functorOfPoints) → Scheme.OpenCover T.left)
#check (AlgebraicGeometry.AlgebraicSpace.ZariskiCover.pullbackOpenCover_X :
  {S : Scheme.{u}} → {F : AlgebraicSpace S} → (𝒰 : ZariskiCover F) →
    {T : Over S} → (a : yoneda.obj T ⟶ F.functorOfPoints) → (i : 𝒰.I₀) →
      (𝒰.pullbackOpenCover a).X i =
        ((𝒰.isOpenImmersion i).presheaf.rep.pullback a).left)
#check (AlgebraicGeometry.AlgebraicSpace.ZariskiCover.pullbackOpenCover_f :
  {S : Scheme.{u}} → {F : AlgebraicSpace S} → (𝒰 : ZariskiCover F) →
    {T : Over S} → (a : yoneda.obj T ⟶ F.functorOfPoints) → (i : 𝒰.I₀) →
      (𝒰.pullbackOpenCover a).f i =
        ((𝒰.isOpenImmersion i).presheaf.rep.snd a).left)
#check (AlgebraicGeometry.AlgebraicSpace.ZariskiCover.mono :
  {S : Scheme.{u}} → {F : AlgebraicSpace S} → (𝒰 : ZariskiCover F) →
    (i : 𝒰.I₀) → Mono (𝒰.f i))
