module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Coherence
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Functoriality.Composition.Basic

/-!
# Computations for composition functoriality on bundled cospans

The naturality comparison of `Cospan.mapComposition` computes at each cospan vertex to the
standard unitor comparison on the successively mapped vertex morphism. These formulas hide
the induced-bicategory wrapper and make the comparison directly usable by componentwise
proofs.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u w' v' u' w'' v'' u''

namespace CategoryTheory.Bicategory.Cospan

variable {B : Type u} [Bicategory.{w, v} B]
variable {B' : Type u'} [Bicategory.{w', v'} B']
variable {B'' : Type u''} [Bicategory.{w'', v''} B'']
variable {S T : Cospan B}

/-- The forward left component of composition-mapping naturality is the standard unitor
comparison on the successively mapped left vertex morphism. -/
@[simp]
theorem mapComposition.naturalityIso.hom.left
    (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') (ψ : S ⟶ T) :
    Hom₂.left (mapComposition.naturalityIso P Q ψ).hom =
      (ρ_ (Q.map (P.map (Hom.left ψ)))).hom ≫
        (λ_ (Q.map (P.map (Hom.left ψ)))).inv := sorry

/-- The forward right component of composition-mapping naturality is the standard unitor
comparison on the successively mapped right vertex morphism. -/
@[simp]
theorem mapComposition.naturalityIso.hom.right
    (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') (ψ : S ⟶ T) :
    Hom₂.right (mapComposition.naturalityIso P Q ψ).hom =
      (ρ_ (Q.map (P.map (Hom.right ψ)))).hom ≫
        (λ_ (Q.map (P.map (Hom.right ψ)))).inv := sorry

/-- The forward base component of composition-mapping naturality is the standard unitor
comparison on the successively mapped common-target morphism. -/
@[simp]
theorem mapComposition.naturalityIso.hom.base
    (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') (ψ : S ⟶ T) :
    Hom₂.base (mapComposition.naturalityIso P Q ψ).hom =
      (ρ_ (Q.map (P.map (Hom.base ψ)))).hom ≫
        (λ_ (Q.map (P.map (Hom.base ψ)))).inv := sorry

/-- The inverse left component of composition-mapping naturality is the inverse standard
unitor comparison on the successively mapped left vertex morphism. -/
@[simp]
theorem mapComposition.naturalityIso.inv.left
    (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') (ψ : S ⟶ T) :
    Hom₂.left (mapComposition.naturalityIso P Q ψ).inv =
      (λ_ (Q.map (P.map (Hom.left ψ)))).hom ≫
        (ρ_ (Q.map (P.map (Hom.left ψ)))).inv := sorry

/-- The inverse right component of composition-mapping naturality is the inverse standard
unitor comparison on the successively mapped right vertex morphism. -/
@[simp]
theorem mapComposition.naturalityIso.inv.right
    (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') (ψ : S ⟶ T) :
    Hom₂.right (mapComposition.naturalityIso P Q ψ).inv =
      (λ_ (Q.map (P.map (Hom.right ψ)))).hom ≫
        (ρ_ (Q.map (P.map (Hom.right ψ)))).inv := sorry

/-- The inverse base component of composition-mapping naturality is the inverse standard
unitor comparison on the successively mapped common-target morphism. -/
@[simp]
theorem mapComposition.naturalityIso.inv.base
    (P : B ⥤ᵖ B') (Q : B' ⥤ᵖ B'') (ψ : S ⟶ T) :
    Hom₂.base (mapComposition.naturalityIso P Q ψ).inv =
      (λ_ (Q.map (P.map (Hom.base ψ)))).hom ≫
        (ρ_ (Q.map (P.map (Hom.base ψ)))).inv := sorry

end CategoryTheory.Bicategory.Cospan
