module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealSubobject.Kernel
public import ReasLib.Topology.Sheaf.Support
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally ringed spaces carried by supported quotient sheaves

For a locally surjective map `𝒪_X ⟶ 𝒜`, the quotient is restricted to its
closed support. The carrier, sheaf, and morphism are explicit data; local-ring
and functoriality assertions are isolated as proof obligations.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.SupportedQuotient

/-- A locally surjective quotient presentation of the structure sheaf of a locally ringed
space. -/
@[stacks 01HM "supported quotient presentation"]
structure Presentation (X : LocallyRingedSpace.{u}) where
  /-- The quotient sheaf of commutative rings. -/
  sheaf : TopCat.Sheaf CommRingCat.{u} X.toTopCat
  /-- The quotient map from the structure sheaf. -/
  projection : X.𝒪 ⟶ sheaf
  /-- The quotient map is locally surjective. -/
  [locallySurjective : Sheaf.IsLocallySurjective projection]

/-- The underlying sheaf of rings whose support carries the quotient. -/
@[stacks 01HM "supported quotient underlying ring sheaf"]
abbrev underlyingRingSheaf {X : LocallyRingedSpace.{u}} (Q : Presentation X) :=
  SheafOfModules.RingedSite.ringSheaf (Opens.grothendieckTopology X.toTopCat) Q.sheaf

/-- The support of a quotient sheaf. -/
@[stacks 01HM "support of a quotient sheaf"]
abbrev support {X : LocallyRingedSpace.{u}} (Q : Presentation X) : Set X :=
  TopCat.Sheaf.ringSheafSupport (underlyingRingSheaf Q)

/-- A point belongs to the quotient support exactly when the germ of the global unit is nonzero. -/
@[stacks 01HM "supported quotient support membership"]
theorem mem_support_iff_one_germ_ne_zero
    {X : LocallyRingedSpace.{u}} (Q : Presentation X) (x : X) :
    x ∈ support Q ↔
      (TopCat.Presheaf.Γgerm (underlyingRingSheaf Q).obj x) 1 ≠ 0 := sorry

/-- The support equipped with its subspace topology. -/
@[stacks 01HM "supported quotient support carrier"]
abbrev carrier {X : LocallyRingedSpace.{u}} (Q : Presentation X) : TopCat.{u} :=
  TopCat.of (support Q)

/-- The inclusion of the support into the ambient topological space. -/
@[stacks 01HM "inclusion of the quotient support"]
def inclusion {X : LocallyRingedSpace.{u}} (Q : Presentation X) :
    carrier Q ⟶ X.toTopCat :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The quotient sheaf restricted to its support. -/
@[stacks 01HM "structure sheaf on the quotient support"]
abbrev structureSheaf {X : LocallyRingedSpace.{u}} (Q : Presentation X) :
    TopCat.Sheaf CommRingCat.{u} (carrier Q) :=
  (TopCat.Sheaf.pullback CommRingCat.{u} (inclusion Q)).obj Q.sheaf

/-- The canonical map from a quotient sheaf to the pushforward of its restriction to the
support. -/
@[stacks 01HM "quotient sheaf support comparison"]
noncomputable def pushforwardComparison
    {X : LocallyRingedSpace.{u}} (Q : Presentation X) :
    Q.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} (inclusion Q)).obj
        (structureSheaf Q) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (inclusion Q)).unit.app Q.sheaf

/-- Restricting a quotient sheaf to its support and pushing forward recovers the original
quotient sheaf. This remains a theorem rather than an `IsIso` instance until its proof is
complete, so unfinished proof debt cannot manufacture an inverse morphism. -/
@[stacks 01HM "supported quotient support comparison isomorphism"]
theorem pushforwardComparison_isIso
    {X : LocallyRingedSpace.{u}} (Q : Presentation X) :
    IsIso (pushforwardComparison Q) := sorry

/-- Every stalk of a locally surjective quotient of a locally ringed structure sheaf is a local
ring. -/
@[stacks 01HM "supported quotient stalk local ring"]
theorem stalk_isLocalRing
    {X : LocallyRingedSpace.{u}} (Q : Presentation X) (z : carrier Q) :
    IsLocalRing ((structureSheaf Q).presheaf.stalk z) := sorry

/-- The locally ringed space carried by the support of a locally surjective quotient sheaf. -/
@[stacks 01HM "supported quotient space"]
noncomputable def space
    {X : LocallyRingedSpace.{u}} (Q : Presentation X) : LocallyRingedSpace.{u} where
  toSheafedSpace :=
    { carrier := carrier Q
      presheaf := (structureSheaf Q).presheaf
      IsSheaf := (structureSheaf Q).2 }
  isLocalRing := stalk_isLocalRing Q

/-- The presheafed-space morphism from the supported quotient to the ambient space. -/
@[stacks 01HM "supported quotient underlying morphism"]
noncomputable def toHom
    {X : LocallyRingedSpace.{u}} (Q : Presentation X) :
    (space Q).toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := inclusion Q
  c := Q.projection.hom ≫ (pushforwardComparison Q).hom

/-- The sheaf map of the supported quotient is the quotient map followed by the
pullback-pushforward adjunction unit. -/
@[simp, stacks 01HM "supported quotient structure-sheaf map"]
theorem toHom_c
    {X : LocallyRingedSpace.{u}} (Q : Presentation X) :
    (toHom Q).c =
      Q.projection.hom ≫ (pushforwardComparison Q).hom := sorry

/-- The stalk maps of the supported quotient morphism are local ring homomorphisms. -/
@[stacks 01HM "supported quotient stalk local homomorphism"]
theorem toHom_isLocalHom
    {X : LocallyRingedSpace.{u}} (Q : Presentation X) (z : space Q) :
    IsLocalHom ((toHom Q).stalkMap z).hom := sorry

/-- The canonical morphism from the supported quotient to its ambient locally ringed space. -/
@[stacks 01HM "supported quotient inclusion"]
noncomputable def ι
    {X : LocallyRingedSpace.{u}} (Q : Presentation X) : space Q ⟶ X where
  toHom := toHom Q
  prop := toHom_isLocalHom Q

/-- Forgetting the local-ring condition recovers the supported quotient presheafed-space map. -/
@[simp, stacks 01HM "supported quotient inclusion underlying morphism"]
theorem ι_toHom
    {X : LocallyRingedSpace.{u}} (Q : Presentation X) :
    (ι Q).toHom = toHom Q := sorry

/-- The underlying map of the supported quotient inclusion is the support inclusion. -/
@[simp, stacks 01HM "supported quotient inclusion underlying map"]
theorem ι_base
    {X : LocallyRingedSpace.{u}} (Q : Presentation X) :
    (ι Q).base = inclusion Q := sorry

/-- The range of the supported quotient inclusion is the support of the quotient sheaf. -/
@[stacks 01HM "supported quotient inclusion range"]
theorem range_ι_base
    {X : LocallyRingedSpace.{u}} (Q : Presentation X) :
    Set.range (ι Q).base = support Q := sorry

/-- The support of a quotient sheaf is a closed subset of the ambient locally ringed space. -/
@[stacks 01HM "closed quotient support"]
theorem isClosed_support
    {X : LocallyRingedSpace.{u}} (Q : Presentation X) :
    IsClosed (support Q) := sorry

/-- The supported quotient inclusion has closed-embedding underlying map. -/
@[stacks 01HM "supported quotient closed embedding"]
theorem ι_isClosedEmbedding
    {X : LocallyRingedSpace.{u}} (Q : Presentation X) :
    Topology.IsClosedEmbedding (ι Q).base := sorry

/-- The sheaf map of the supported quotient inclusion is locally surjective. -/
@[stacks 01HM "supported quotient local surjectivity"]
instance ι_isLocallySurjective
    {X : LocallyRingedSpace.{u}} (Q : Presentation X) :
    Sheaf.IsLocallySurjective
      (Hom.commRingSheafPushforwardMap (ι Q)) := sorry

/-- The kernel ideal subobject of a supported quotient inclusion is the kernel subobject of its
quotient map. -/
@[simp, stacks 01HM "supported quotient kernel ideal"]
theorem kernelIdealSubobject_ι
    {X : LocallyRingedSpace.{u}} (Q : Presentation X) :
    Hom.kernelIdealSubobject (ι Q) =
      KernelIdeal.subobject.{u, u, u} Q.projection := sorry

end AlgebraicGeometry.LocallyRingedSpace.SupportedQuotient
