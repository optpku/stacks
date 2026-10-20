module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.CategoryTheory.Fibered.InheritedTopology

/-!
# Sheaves on a category fibred in groupoids

A presheaf on a category fibred in groupoids over `(Sch/S)_fppf` is a sheaf
for a standard topology `τ` when it is a sheaf on the associated inherited
site. The corresponding sheaf category is mathlib's `Sheaf` for that topology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w uA wA

namespace AlgebraicGeometry.FiberedInGroupoids

/-- A presheaf on a category fibred in groupoids over `(Sch/S)_fppf` is a sheaf
for the standard topology `τ` when it is a sheaf on the associated inherited
`τ`-site. -/
abbrev IsSheafFor {S : Scheme.{u}} {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ Over S) [Functor.IsFibered.InGroupoids p] (τ : StandardTopology)
    {A : Type uA} [Category.{wA} A] (F : 𝒳ᵒᵖ ⥤ A) : Prop :=
  Presheaf.IsSheaf (p.inheritedTopology (τ.overTopology S)) F

/-- The category of `A`-valued sheaves on the associated `τ`-site of a category
fibred in groupoids over `(Sch/S)_fppf`. -/
abbrev Sheaves {S : Scheme.{u}} {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ Over S) [Functor.IsFibered.InGroupoids p] (τ : StandardTopology)
    (A : Type uA) [Category.{wA} A] :=
  Sheaf (p.inheritedTopology (τ.overTopology S)) A

/-- `IsSheafFor` is the canonical sheaf predicate on the inherited `τ`-site. -/
theorem isSheafFor_iff {S : Scheme.{u}} {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ Over S) [Functor.IsFibered.InGroupoids p] (τ : StandardTopology)
    {A : Type uA} [Category.{wA} A] (F : 𝒳ᵒᵖ ⥤ A) :
    IsSheafFor p τ F ↔ Presheaf.IsSheaf (p.inheritedTopology (τ.overTopology S)) F :=
  sorry

/-- A Zariski sheaf is a sheaf for the inherited Zariski topology. -/
theorem isSheafFor_zariski {S : Scheme.{u}} {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ Over S) [Functor.IsFibered.InGroupoids p]
    {A : Type uA} [Category.{wA} A] (F : 𝒳ᵒᵖ ⥤ A) :
    IsSheafFor p StandardTopology.zariski F ↔
      Presheaf.IsSheaf (p.inheritedTopology (Scheme.zariskiTopology.over S)) F :=
  sorry

/-- An étale sheaf is a sheaf for the inherited étale topology. -/
theorem isSheafFor_etale {S : Scheme.{u}} {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ Over S) [Functor.IsFibered.InGroupoids p]
    {A : Type uA} [Category.{wA} A] (F : 𝒳ᵒᵖ ⥤ A) :
    IsSheafFor p StandardTopology.etale F ↔
      Presheaf.IsSheaf
        (p.inheritedTopology (StandardTopology.etale.overTopology S)) F :=
  sorry

/-- A smooth sheaf is a sheaf for the inherited smooth topology. -/
theorem isSheafFor_smooth {S : Scheme.{u}} {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ Over S) [Functor.IsFibered.InGroupoids p]
    {A : Type uA} [Category.{wA} A] (F : 𝒳ᵒᵖ ⥤ A) :
    IsSheafFor p StandardTopology.smooth F ↔
      Presheaf.IsSheaf
        (p.inheritedTopology (StandardTopology.smooth.overTopology S)) F :=
  sorry

/-- A syntomic sheaf is a sheaf for the inherited syntomic topology. -/
theorem isSheafFor_syntomic {S : Scheme.{u}} {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ Over S) [Functor.IsFibered.InGroupoids p]
    {A : Type uA} [Category.{wA} A] (F : 𝒳ᵒᵖ ⥤ A) :
    IsSheafFor p StandardTopology.syntomic F ↔
      Presheaf.IsSheaf
        (p.inheritedTopology (StandardTopology.syntomic.overTopology S)) F :=
  sorry

/-- An fppf sheaf is a sheaf for the inherited fppf topology. -/
theorem isSheafFor_fppf {S : Scheme.{u}} {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ Over S) [Functor.IsFibered.InGroupoids p]
    {A : Type uA} [Category.{wA} A] (F : 𝒳ᵒᵖ ⥤ A) :
    IsSheafFor p StandardTopology.fppf F ↔
      Presheaf.IsSheaf (p.inheritedTopology (Scheme.fppfTopology.over S)) F :=
  sorry

/-- Objects of `Sheaves p τ A` are sheaves for the associated `τ`-site. -/
theorem sheaves_obj {S : Scheme.{u}} {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ Over S) [Functor.IsFibered.InGroupoids p] (τ : StandardTopology)
    (A : Type uA) [Category.{wA} A] (F : Sheaves p τ A) :
    IsSheafFor p τ F.obj :=
  sorry

end AlgebraicGeometry.FiberedInGroupoids
