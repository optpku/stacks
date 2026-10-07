module

public import ReasLib.AlgebraicGeometry.RingedSite.Basic
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

/-- The projection of a category fibred in groupoids is continuous for each
associated `τ`-topology. -/
instance associatedProjection_isContinuous (𝒳 : GroupoidsOver S) (τ : StandardTopology) :
    𝒳.p.IsContinuous (𝒳.associatedTopology τ) (τ.overTopology S) :=
  Functor.inheritedTopology.isContinuous 𝒳.p (τ.overTopology S)

/-- The structure sheaf `𝒪_𝒳` on the associated `τ`-site of a category fibred
in groupoids, obtained as the inverse image `p⁻¹ 𝒪` of the big `τ`-structure
sheaf of `S`. -/
def associatedStructureSheaf (𝒳 : GroupoidsOver S) (τ : StandardTopology) :
    Sheaf (𝒳.associatedTopology τ) RingCat.{u} :=
  (𝒳.p.sheafPushforwardContinuous RingCat.{u}
      (𝒳.associatedTopology τ) (τ.overTopology S)).obj
    (StandardTopology.Big.structureSheaf τ S)

/-- Sections of `𝒪_𝒳` at `x` agree with sections of the big `τ`-structure sheaf
at `p(x)`. -/
theorem associatedStructureSheaf_obj_eq_big {𝒳 : GroupoidsOver S}
    (τ : StandardTopology) (x : 𝒳.total) :
    (associatedStructureSheaf 𝒳 τ).obj.obj (op x) =
      (StandardTopology.Big.structureSheaf τ S).obj.obj (op (𝒳.p.obj x)) :=
  sorry

/-- For an object `x` of `𝒳` lying over `U`, the value of `𝒪_𝒳` at `x` is
`Γ(U, 𝒪_U)`. -/
theorem associatedStructureSheaf_obj {𝒳 : GroupoidsOver S}
    (τ : StandardTopology) (x : 𝒳.total) :
    (associatedStructureSheaf 𝒳 τ).obj.obj (op x) =
      RingCat.of Γ((𝒳.p.obj x).left, ⊤) :=
  sorry

/-- The associated `τ`-ringed site `(𝒳_τ, 𝒪_𝒳)` of a category fibred in
groupoids over `(Sch/S)_fppf`. -/
def associatedRingedSite (𝒳 : GroupoidsOver S) (τ : StandardTopology) :
    RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf (𝒳.associatedTopology τ) (associatedStructureSheaf 𝒳 τ)

/-- The topology of `associatedRingedSite 𝒳 τ` is the associated `τ`-topology of
`𝒳`. -/
theorem associatedRingedSite_siteTopology (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) :
    (associatedRingedSite 𝒳 τ).siteTopology = 𝒳.associatedTopology τ :=
  sorry

/-- The structure sheaf of `associatedRingedSite 𝒳 τ` is `𝒪_𝒳`. -/
theorem associatedRingedSite_structureSheaf (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) :
    (associatedRingedSite 𝒳 τ).structureSheaf = associatedStructureSheaf 𝒳 τ :=
  sorry

/-- At `τ = fppf`, the associated ringed site is the fppf ringed site of
Definition 96.6.1. -/
theorem associatedRingedSite_fppf (𝒳 : GroupoidsOver S) :
    associatedRingedSite 𝒳 .fppf = ringedSite 𝒳 :=
  sorry

end AlgebraicGeometry.GroupoidsOver
