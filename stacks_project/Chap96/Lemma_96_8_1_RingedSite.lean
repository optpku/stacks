module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.RingedSite
public import ReasLib.AlgebraicGeometry.GroupoidsOver.AssociatedStructureSheaf
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import stacks_project.Chap96.Definition_96_6_1_StructureSheaf

/-!
# Associated ringed sites of categories fibred in groupoids

A category fibred in groupoids over `(Sch/S)_fppf` inherits a ringed site
`(𝒳_τ, 𝒪_𝒳)` from each of the five big sites of `S`, by continuous
pushforward of the big `τ`-structure sheaf along the projection.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

#check (AlgebraicGeometry.GroupoidsOver.associatedStructureSheaf :
  ∀ {S : Scheme.{u}} (𝒳 : GroupoidsOver S) (τ : StandardTopology),
    Sheaf (𝒳.associatedTopology τ) RingCat.{u})

#check (AlgebraicGeometry.GroupoidsOver.associatedStructureSheaf_obj_eq_big :
  ∀ {S : Scheme.{u}} {𝒳 : GroupoidsOver S} (τ : StandardTopology) (x : 𝒳.total),
    (associatedStructureSheaf 𝒳 τ).obj.obj (op x) =
      (StandardTopology.Big.structureSheaf τ S).obj.obj (op (𝒳.p.obj x)))

#check (AlgebraicGeometry.GroupoidsOver.associatedStructureSheaf_obj :
  ∀ {S : Scheme.{u}} {𝒳 : GroupoidsOver S} (τ : StandardTopology) (x : 𝒳.total),
    (associatedStructureSheaf 𝒳 τ).obj.obj (op x) =
      RingCat.of Γ((𝒳.p.obj x).left, ⊤))

#check (AlgebraicGeometry.GroupoidsOver.associatedRingedSite :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (τ : StandardTopology),
    RingedSite.{u + 1, u, u})

#check (AlgebraicGeometry.GroupoidsOver.associatedRingedSite_siteTopology :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (τ : StandardTopology),
    (associatedRingedSite X τ).siteTopology = X.associatedTopology τ)

#check (AlgebraicGeometry.GroupoidsOver.associatedRingedSite_structureSheaf :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (τ : StandardTopology),
    (associatedRingedSite X τ).structureSheaf = associatedStructureSheaf X τ)

#check (AlgebraicGeometry.GroupoidsOver.associatedRingedSite_fppf :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S), associatedRingedSite X .fppf = ringedSite X)

end AlgebraicGeometry.GroupoidsOver
