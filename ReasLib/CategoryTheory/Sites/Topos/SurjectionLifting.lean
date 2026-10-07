module

public import ReasLib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.CategoryTheory.Sites.Topos.Morphism

/-!
# Surjection lifting for morphisms of topoi

For a morphism of topoi, this leaf relates preservation of locally surjective
maps by direct image to the intrinsic lifting property for covers of inverse
images.  The generic local-surjectivity and epimorphism API belongs to the
parent `Sites` layer.
-/

@[expose] public section

open CategoryTheory

universe uC uD vC vD w

namespace CategoryTheory.MorphismOfTopoiIn

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- A morphism of topoi has surjection lifting when every locally surjective
map to an inverse image is dominated by the inverse image of a locally
surjective map in the target topos.  This is an explicit proposition rather
than a typeclass: applications naturally carry the lifting witness as a
hypothesis and should not need a local instance. -/
def HasSurjectionLifting (f : MorphismOfTopoiIn J K) : Prop :=
  ∀ {F : Sheaf K (Type w)} {G : Sheaf J (Type w)}
    (phi : F ⟶ f.inverseImage.obj G),
    Sheaf.IsLocallySurjective phi →
      ∃ (G' : Sheaf J (Type w)) (pi : G' ⟶ G),
        Sheaf.IsLocallySurjective pi ∧
          ∃ iota : f.inverseImage.obj G' ⟶ F,
            iota ≫ phi = f.inverseImage.map pi

namespace HasSurjectionLifting

/-- Apply an explicit surjection-lifting witness to a locally surjective map
into an inverse image. -/
theorem lift
    {f : MorphismOfTopoiIn J K}
    (h : f.HasSurjectionLifting)
    {F : Sheaf K (Type w)} {G : Sheaf J (Type w)}
    (phi : F ⟶ f.inverseImage.obj G)
    (hphi : Sheaf.IsLocallySurjective phi) :
    ∃ (G' : Sheaf J (Type w)) (pi : G' ⟶ G),
      Sheaf.IsLocallySurjective pi ∧
        ∃ iota : f.inverseImage.obj G' ⟶ F,
          iota ≫ phi = f.inverseImage.map pi := sorry

/-- Direct image preserving locally surjective morphisms supplies the
surjection-lifting property. -/
theorem of_preservesLocallySurjective
    {f : MorphismOfTopoiIn J K}
    (h : f.pushforward.PreservesLocallySurjective) :
    f.HasSurjectionLifting := sorry

/-- The surjection-lifting property forces direct image to preserve locally
surjective morphisms. -/
theorem preservesLocallySurjective
    {f : MorphismOfTopoiIn J K}
    (h : f.HasSurjectionLifting) :
    f.pushforward.PreservesLocallySurjective := sorry

/-- A direct image preserves locally surjective morphisms exactly when the
associated morphism of topoi has surjection lifting. -/
theorem iff_preservesLocallySurjective
    (f : MorphismOfTopoiIn J K) :
    f.HasSurjectionLifting ↔ f.pushforward.PreservesLocallySurjective := sorry

/-- With sheafification on both sites, the surjection-lifting property is
equivalent to direct image preserving epimorphisms. -/
theorem preservesEpimorphisms_iff
    (f : MorphismOfTopoiIn J K)
    [HasSheafify J (Type w)] [HasSheafify K (Type w)] :
    f.pushforward.PreservesEpimorphisms ↔ f.HasSurjectionLifting := sorry

end HasSurjectionLifting

end CategoryTheory.MorphismOfTopoiIn
