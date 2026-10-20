module

public import ReasLib.CategoryTheory.Adjunction.LeftExact
public import ReasLib.CategoryTheory.Sites.Topos.Morphism

/-!
# Properties of topos morphisms

Embeddings (full+faithful direct image), surjections (faithful inverse image),
localic morphisms (both), and connected morphisms (full+faithful inverse image).
-/

@[expose] public section

universe u₁ u₂ u₃ v₁ v₂ v₃ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace MorphismOfTopoiIn

/-- A morphism of topoi is a surjection when its inverse image is faithful. -/
class IsSurjection (f : MorphismOfTopoiIn J K) : Prop where
  faithful : f.inverseImage.Faithful

/-- A surjection iff inverse image faithful. -/
theorem isSurjection_iff (f : MorphismOfTopoiIn J K) :
    f.IsSurjection ↔ f.inverseImage.Faithful := sorry

/-- A morphism of topoi is localic when it is both an embedding and a surjection. -/
class IsLocalic (f : MorphismOfTopoiIn J K) extends IsEmbedding f, IsSurjection f : Prop

/-- A morphism is localic iff both an embedding and a surjection. -/
theorem isLocalic_iff (f : MorphismOfTopoiIn J K) :
    IsLocalic f ↔ IsEmbedding f ∧ IsSurjection f := sorry

/-- A morphism of topoi is connected when its inverse image is fully faithful. -/
class IsConnected (f : MorphismOfTopoiIn J K) : Prop where
  full : f.inverseImage.Full
  faithful : f.inverseImage.Faithful

/-- Connected implies surjection. -/
instance (f : MorphismOfTopoiIn J K) [f.IsConnected] : f.IsSurjection := sorry

/-- The identity is an embedding. -/
instance id_isEmbedding : (MorphismOfTopoiIn.id J).IsEmbedding := sorry

/-- The identity is a surjection. -/
instance id_isSurjection : (MorphismOfTopoiIn.id J).IsSurjection := sorry

/-- An embedding's counit is an iso. -/
theorem IsEmbedding.counit_isIso (f : MorphismOfTopoiIn J K) [f.IsEmbedding] :
    IsIso f.adjunction.counit := sorry

/-- An embedding's direct image reflects isomorphisms. -/
instance (f : MorphismOfTopoiIn J K) [f.IsEmbedding] :
    f.pushforward.ReflectsIsomorphisms := sorry

/-- Composition of embeddings is an embedding. -/
instance comp_isEmbedding {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    (f : MorphismOfTopoiIn J K) (g : MorphismOfTopoiIn K L)
    [f.IsEmbedding] [g.IsEmbedding] :
    (f.comp g).IsEmbedding := sorry

/-- Composition of surjections is a surjection. -/
instance comp_isSurjection {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    (f : MorphismOfTopoiIn J K) (g : MorphismOfTopoiIn K L)
    [f.IsSurjection] [g.IsSurjection] :
    (f.comp g).IsSurjection := sorry

end MorphismOfTopoiIn

end CategoryTheory
