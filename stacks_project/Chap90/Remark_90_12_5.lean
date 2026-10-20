module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Over
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.At
import StacksCheckRecall

/-!
# Tangent spaces of categories cofibered in groupoids

The tangent space and differential of a predeformation category globalize to an
arbitrary category cofibered in groupoids over `C_Λ` by passing to the residue
slice of Remark 90.6.4.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor
open scoped Bicategory

universe u v w

/- Remark 90.12.5 (1): Let F be a category cofibered in groupoids over C_Λ, and let
x be an object of F(k). As in Remark 90.6.4, we get a predeformation category F_x.
We define T_x F = T F_x to be the tangent space of F at x. This is
`Functor.tangentSpaceAt`. -/
@[stacks 06IK]
#check (CategoryTheory.Functor.tangentSpaceAt :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type v} [Category.{w} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x : p.Fiber (residue Λ k)), Type (max v w))

/- Remark 90.12.5 (2): If φ : F ⟶ G is a morphism of categories cofibered in groupoids
over C_Λ and x is an object of F(k), then there is an induced morphism
φ_x : F_x ⟶ G_{φ(x)}. This is `BasedFunctor.sliceMap`. -/
@[stacks 06IK]
#check (CategoryTheory.BasedFunctor.sliceMap :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F G : Type v} [Category.{w} F] [Category.{w} G]
    {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
    [IsFibered.InGroupoids p.op] [IsFibered.InGroupoids q.op]
    (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)),
    BasedCategory.ofFunctor (CategoryTheory.Functor.sliceAt p x) ⥤ᵇ
      BasedCategory.ofFunctor
        (CategoryTheory.Functor.sliceAt q (CategoryTheory.BasedFunctor.objAt φ x)))

/- Remark 90.12.5 (3): We define the differential d_x φ : T_x F ⟶ T_{φ(x)} G of φ at x
to be the map d φ_x : T F_x ⟶ T G_{φ(x)}. This is `BasedFunctor.differentialAt`. -/
@[stacks 06IK]
#check (CategoryTheory.BasedFunctor.differentialAt :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F G : Type v} [Category.{w} F] [Category.{w} G]
    {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
    [IsFibered.InGroupoids p.op] [IsFibered.InGroupoids q.op]
    (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)),
    CategoryTheory.Functor.tangentSpaceAt p x →
      CategoryTheory.Functor.tangentSpaceAt q (CategoryTheory.BasedFunctor.objAt φ x))

/- Remark 90.12.5 (4): If both F and G satisfy (S2) then all of these tangent spaces
have a natural k-vector space structure (use Lemmas 90.10.6 and 90.12.4). -/
@[stacks 06IK]
#check (CategoryTheory.Functor.instModule_tangentSpaceAt :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type v} [Category.{w} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    [HasSchlessingerS2 p] (x : p.Fiber (residue Λ k)),
    Module k (CategoryTheory.Functor.tangentSpaceAt p x))

/- Remark 90.12.5 (5): If both F and G satisfy (S2) then all the differentials
d_x φ : T_x F ⟶ T_{φ(x)} G are k-linear (use Lemmas 90.10.6 and 90.12.4). -/
@[stacks 06IK]
#check (CategoryTheory.BasedFunctor.isLinearMap_differentialAt :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F G : Type v} [Category.{w} F] [Category.{w} G]
    {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
    [IsFibered.InGroupoids p.op] [IsFibered.InGroupoids q.op]
    [HasSchlessingerS2 p] [HasSchlessingerS2 q]
    (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)),
    IsLinearMap k (CategoryTheory.BasedFunctor.differentialAt φ x))
