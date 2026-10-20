module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Projection
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Map

/-!
# Smoothness on associated predeformation categories

A 1-morphism of categories fibred in groupoids over a locally Noetherian scheme
is smooth on predeformations when every induced map of predeformation categories
at a finite-type field is a smooth morphism over `ArtinianLocalAlgCat`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver.Predeformation
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (X : GroupoidsOver S) (x0 : X.p.Fiber (Over.mk kToS))

/-- The projection of the predeformation category of a residue object is
cofibered in groupoids over the category of Artinian local algebras. -/
instance instIsFiberedInGroupoids_predeformation :
    Functor.IsFibered.InGroupoids (predeformation openImmersion h_factor X x0).p.op :=
  (instIsPredeformationCategory_predeformationFunctor
      X openImmersion kToS h_factor x0).isCofiberedInGroupoids

end AlgebraicGeometry.GroupoidsOver.Predeformation

namespace AlgebraicGeometry.Groupoids.Hom

section

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X Y : GroupoidsOver S}

/-- The induced map of predeformation categories `ℱ_{X, k, x0} ⟶ ℱ_{Y, k, f(x0)}`
is a smooth morphism of categories cofibered in groupoids over
`ArtinianLocalAlgCat Λ k`. -/
abbrev IsSmoothAt (f : X ⟶ Y) {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : X.p.Fiber (Over.mk kToS)) :=
  BasedFunctor.IsSmooth (map openImmersion h_factor f x0)

/-- A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over `(Sch/S)_fppf`
is smooth on predeformations when, for every field `k` of finite type over a
locally Noetherian scheme `S` and every object `x0` of `X` over `Spec(k)`, the
induced map of predeformation categories is smooth. -/
class IsSmoothOnPredeformations (f : X ⟶ Y) : Prop where
  /-- For every finite-type field `k` over `S` and every `x0` over `Spec(k)`,
  the induced map `ℱ_{X, k, x0} ⟶ ℱ_{Y, k, f(x0)}` is smooth. -/
  isSmoothAt : ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k]
    [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : X.p.Fiber (Over.mk kToS)),
    IsSmoothAt f openImmersion kToS h_factor x0

end

namespace IsSmoothOnPredeformations

/-- The identity 1-morphism of a category fibred in groupoids is smooth on
predeformations. -/
instance id {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S} :
    IsSmoothOnPredeformations (𝟙 X) := sorry

/-- The composite of two 1-morphisms of categories fibred in groupoids over a
locally Noetherian scheme that are smooth on predeformations is smooth on
predeformations. -/
@[stacks 07XU]
instance comp
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSmoothOnPredeformations f] [IsSmoothOnPredeformations g] :
    IsSmoothOnPredeformations (f ≫ g) :=
  sorry

/-- A 1-morphism that is smooth on predeformations induces a smooth map of
predeformation categories at every finite-type field and residue object. -/
theorem spec {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [IsSmoothOnPredeformations f] :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k]
      (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
      (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
      (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
      (x0 : X.p.Fiber (Over.mk kToS)),
      IsSmoothAt f openImmersion kToS h_factor x0 :=
  sorry

end IsSmoothOnPredeformations

section

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X Y : GroupoidsOver S} (f : X ⟶ Y)
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (x0 : X.p.Fiber (Over.mk kToS))

/-- Pointwise smoothness on predeformations is smoothness of the induced based
functor of predeformation categories. -/
theorem isSmoothAt_iff :
    IsSmoothAt f openImmersion kToS h_factor x0 ↔
      BasedFunctor.IsSmooth (map openImmersion h_factor f x0) :=
  sorry

/-- Smoothness on predeformations specialises to smoothness of the induced map at
a given finite-type field and residue object. -/
instance instIsSmoothAt_of_isSmoothOnPredeformations [IsSmoothOnPredeformations f] :
    IsSmoothAt f openImmersion kToS h_factor x0 := sorry

end

/-- A morphism of categories fibred in groupoids is smooth on predeformations
if and only if its induced map of predeformation categories is smooth at every
finite-type field-valued point and every residue object. -/
theorem isSmoothOnPredeformations_iff {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    IsSmoothOnPredeformations f ↔
      ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
        [Module.Finite Λ k]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
        (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
        (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
        (x0 : X.p.Fiber (Over.mk kToS)),
        IsSmoothAt f openImmersion kToS h_factor x0 :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
