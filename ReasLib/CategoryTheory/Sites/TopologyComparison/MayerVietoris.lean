module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.AbsoluteDerived
public import ReasLib.CategoryTheory.Sites.Derived.Sections.MayerVietoris
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Mayer--Vietoris descent across a topology comparison

This leaf combines the absolute topology-comparison right-derived functor with the canonical
Mayer--Vietoris condition on derived sections. The cochain realization API remains in the
derived-sections owner and is not repeated here.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped GrothendieckTopologyDerivedSections

noncomputable section

universe u v uι

namespace CategoryTheory.GrothendieckTopology.Derived.Absolute.MayerVietoris

open CategoryTheory.GrothendieckTopology.Derived.Sections.MayerVietoris

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}
variable [HasSheafify τ AddCommGrpCat.{max u v}]
variable [HasSheafify τ' AddCommGrpCat.{max u v}]
variable [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat τ')]

/-- A square whose `τ`-sheafified representables form a pushout, with monomorphic map from its
overlap, satisfies the canonical derived Mayer--Vietoris condition for every `τ'`-object in the
essential image of the topology-comparison right-derived direct image. -/
@[stacks 0F19 "Mayer--Vietoris descent across a topology comparison"]
theorem condition_of_essImage
    [HasWeakSheafify τ (Type (max u v))]
    (hle : τ' ≤ τ)
    [Functor.HasRightDerivedFunctor
      (Functor.Homotopy.toDerived (Absolute.pushforward hle)) (Absolute.qis τ)]
    (S : Square C)
    (hpushout :
      IsPushout
        (τ.sheafifiedRepresentableMap S.toY)
        (τ.sheafifiedRepresentableMap S.toZ)
        (τ.sheafifiedRepresentableMap S.inY)
        (τ.sheafifiedRepresentableMap S.inZ))
    (hmono : Mono (τ.sheafifiedRepresentableMap S.toY))
    (K' : DerivedCategory (SiteAbelianSheafCat τ'))
    (hK' : Functor.essImage (Absolute.rightDerived hle) K') :
    S.Condition τ' K' := sorry

/-- If a family of commutative squares detects when a `τ'`-sheaf of sets is a `τ`-sheaf and the
canonical Mayer--Vietoris condition holds on the essential image of the topology-comparison
right-derived direct image, then essential-image membership for a bounded-below object is
equivalent to the Mayer--Vietoris condition on every square in the family. -/
@[stacks 0F18 "bounded-below essential-image criterion"]
theorem essImage_iff_condition
    {ι : Type uι}
    (hle : τ' ≤ τ)
    [Functor.HasRightDerivedFunctor
      (Functor.Homotopy.toDerived (Absolute.pushforward hle)) (Absolute.qis τ)]
    (S : ι → Square C)
    (hSheaf :
      ∀ ⦃F' : Cᵒᵖ ⥤ Type (max u v)⦄,
        Presheaf.IsSheaf τ' F' →
          (∀ i : ι,
            IsPullback
              (F'.map (S i).inY.op)
              (F'.map (S i).inZ.op)
              (F'.map (S i).toY.op)
              (F'.map (S i).toZ.op)) →
            Presheaf.IsSheaf τ F')
    (hcondition :
      ∀ ⦃L' : DerivedCategory (SiteAbelianSheafCat τ')⦄,
        Functor.essImage (Absolute.rightDerived hle) L' →
          ∀ i : ι, (S i).Condition τ' L')
    (K' : DerivedCategory.Plus (SiteAbelianSheafCat τ')) :
    Functor.essImage
        (Absolute.rightDerived hle)
        (DerivedCategory.Plus.ι.obj K') ↔
      ∀ i : ι, (S i).Condition τ' (DerivedCategory.Plus.ι.obj K') := sorry

/-! The source-facing family form keeps the pushout and monomorphism hypotheses explicit.  The
generic theorem above is useful when those hypotheses have already been packaged into
`hcondition`; this companion is the faithful entry point for textbook callers. -/

/-- A family of `τ`-sheafified-representable Mayer--Vietoris squares, together with the sheaf
detection hypothesis, characterizes the essential image of the topology-comparison right-derived
direct image on bounded-below objects. -/
@[stacks 0F18 "source-facing Mayer--Vietoris family criterion"]
theorem essImage_iff_condition_of_mayerVietoris_family
    {ι : Type uι}
    (hle : τ' ≤ τ)
    [Functor.HasRightDerivedFunctor
      (Functor.Homotopy.toDerived (Absolute.pushforward hle)) (Absolute.qis τ)]
    (S : ι → Square C)
    (hpushout :
      ∀ i : ι,
        IsPushout
          (τ.sheafifiedRepresentableMap (S i).toY)
          (τ.sheafifiedRepresentableMap (S i).toZ)
          (τ.sheafifiedRepresentableMap (S i).inY)
          (τ.sheafifiedRepresentableMap (S i).inZ))
    (hmono :
      ∀ i : ι,
        Mono (τ.sheafifiedRepresentableMap (S i).toY))
    (hSheaf :
      ∀ ⦃F' : Cᵒᵖ ⥤ Type (max u v)⦄,
        Presheaf.IsSheaf τ' F' →
          (∀ i : ι,
            IsPullback
              (F'.map (S i).inY.op)
              (F'.map (S i).inZ.op)
              (F'.map (S i).toY.op)
              (F'.map (S i).toZ.op)) →
            Presheaf.IsSheaf τ F')
    (K' : DerivedCategory.Plus (SiteAbelianSheafCat τ')) :
    Functor.essImage
        (Absolute.rightDerived hle)
        (DerivedCategory.Plus.ι.obj K') ↔
      ∀ i : ι, (S i).Condition τ' (DerivedCategory.Plus.ι.obj K') := sorry

end CategoryTheory.GrothendieckTopology.Derived.Absolute.MayerVietoris

end
