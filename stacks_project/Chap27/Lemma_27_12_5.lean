module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.MorphismFunctor
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

#check (AlgebraicGeometry.Proj.degreeOpen :
  ∀ {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ),
    (AlgebraicGeometry.Proj 𝒜).Opens)

#check (AlgebraicGeometry.Proj.DegreeOpenFactorization :
  ∀ {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (Y : AlgebraicGeometry.Scheme.{u}), Type u)

#check (AlgebraicGeometry.Proj.DegreeOpenFactorization.toProj :
  ∀ {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : AlgebraicGeometry.Scheme.{u}}
    (x : AlgebraicGeometry.Proj.DegreeOpenFactorization 𝒜 Y),
    Y ⟶ AlgebraicGeometry.Proj 𝒜)

#check (AlgebraicGeometry.Proj.DegreeOpenFactorization.setoid :
  ∀ {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (Y : AlgebraicGeometry.Scheme.{u}),
    Setoid (AlgebraicGeometry.Proj.DegreeOpenFactorization 𝒜 Y))

#check (AlgebraicGeometry.Proj.DegreeOpenFactorizationClass :
  ∀ {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (Y : AlgebraicGeometry.Scheme.{u}), Type u)

#check (AlgebraicGeometry.Proj.DegreeOpenFactorization.pullback :
  ∀ {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y Z : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ Z) (x : AlgebraicGeometry.Proj.DegreeOpenFactorization 𝒜 Z),
    AlgebraicGeometry.Proj.DegreeOpenFactorization 𝒜 Y)

#check (AlgebraicGeometry.Proj.DegreeOpenFactorization.pullback_respects :
  ∀ {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y Z : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ Z) {x y : AlgebraicGeometry.Proj.DegreeOpenFactorization 𝒜 Z},
    (AlgebraicGeometry.Proj.DegreeOpenFactorization.setoid 𝒜 Z).r x y →
      (AlgebraicGeometry.Proj.DegreeOpenFactorization.setoid 𝒜 Y).r
        (AlgebraicGeometry.Proj.DegreeOpenFactorization.pullback 𝒜 f x)
        (AlgebraicGeometry.Proj.DegreeOpenFactorization.pullback 𝒜 f y))

#check (AlgebraicGeometry.Proj.degreeOpenFactorizationMap :
  ∀ {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {Y Z : Opposite (AlgebraicGeometry.Scheme.{u})} (f : Y ⟶ Z),
    AlgebraicGeometry.Proj.DegreeOpenFactorizationClass 𝒜 Y.unop ⟶
      AlgebraicGeometry.Proj.DegreeOpenFactorizationClass 𝒜 Z.unop)

#check (AlgebraicGeometry.Proj.degreeOpenFactorizationMap_id :
  ∀ {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (Y : Opposite (AlgebraicGeometry.Scheme.{u})),
    AlgebraicGeometry.Proj.degreeOpenFactorizationMap 𝒜 (𝟙 Y) =
      𝟙 (AlgebraicGeometry.Proj.DegreeOpenFactorizationClass 𝒜 Y.unop))

#check (AlgebraicGeometry.Proj.degreeOpenFactorizationMap_comp :
  ∀ {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {Y Z W : Opposite (AlgebraicGeometry.Scheme.{u})} (f : Y ⟶ Z) (g : Z ⟶ W),
    AlgebraicGeometry.Proj.degreeOpenFactorizationMap 𝒜 (f ≫ g) =
      AlgebraicGeometry.Proj.degreeOpenFactorizationMap 𝒜 f ≫
        AlgebraicGeometry.Proj.degreeOpenFactorizationMap 𝒜 g)

#check (AlgebraicGeometry.Proj.degreeOpenFactorizationFunctor :
  ∀ {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜],
    Opposite (AlgebraicGeometry.Scheme.{u}) ⥤ Type u)

#check (AlgebraicGeometry.Proj.degreeOpen_le_of_dvd :
  ∀ {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {d d' : {n : ℕ // 1 ≤ n}},
    d.1 ∣ d'.1 → AlgebraicGeometry.Proj.degreeOpen 𝒜 d.1 ≤
      AlgebraicGeometry.Proj.degreeOpen 𝒜 d'.1)

#check (AlgebraicGeometry.Proj.MorphismFunctor :
  ∀ {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜], Type (u + 1))

#check (AlgebraicGeometry.Proj.MorphismFunctor.toFunctor :
  ∀ {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (F : AlgebraicGeometry.Proj.MorphismFunctor 𝒜),
    Opposite (AlgebraicGeometry.Scheme.{u}) ⥤ Type u)

#check (AlgebraicGeometry.Proj.MorphismFunctor.ofIso :
  ∀ {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (F : AlgebraicGeometry.Proj.MorphismFunctor 𝒜)
    (G : CategoryTheory.Sheaf AlgebraicGeometry.Scheme.zariskiTopology (Type u))
    (e : F.toFunctor ≅ G.1), AlgebraicGeometry.Proj.MorphismFunctor 𝒜)

/- Lemma 27.12.5: Let `S` be a graded ring and let `X = Proj(S)`. The functor assembled from
the positive-degree charts is represented by `X`. -/
@[stacks 01NC] #check (AlgebraicGeometry.Proj.MorphismFunctor.isRepresentedBy :
  ∀ {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (F : AlgebraicGeometry.Proj.MorphismFunctor 𝒜),
    ∃ x : F.toFunctor.obj (Opposite.op (AlgebraicGeometry.Proj 𝒜)),
      F.toFunctor.IsRepresentedBy x)
