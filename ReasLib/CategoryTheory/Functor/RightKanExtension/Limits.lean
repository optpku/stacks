/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.RightKanExtension.Map
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Limits of individually chosen right Kan extensions

Right Kan extension is usually exposed as a functor only after every object in the source
functor category is known to admit an extension.  This file supplies the objectwise layer: for a
single diagram, it only asks for the extensions of the objects occurring in that diagram and of
its limit.

The limit witness is constructed explicitly.  A cone over the diagram of right Kan extensions is
first restricted along the original functor, then mapped into the source limit, and finally lifted
through the universal property of the chosen right Kan extension.  Thus the non-proof data does
not rely on a placeholder for an entire `IsLimit` structure.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightKanExtension

variable {J : Type u₀} [Category.{v₀} J]
variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable (L : A ⥤ B)

namespace diagram

variable (K : J ⥤ (A ⥤ C)) [∀ j, L.HasRightKanExtension (K.obj j)]

/-- The objectwise chosen right Kan extension assignment preserves identity maps. -/
@[stacks 018C "identity law for the diagram of chosen right Kan extensions"]
theorem map_id (j : J) :
    map L (K.map (𝟙 j)) = 𝟙 (L.rightKanExtension (K.obj j)) := sorry

/-- The objectwise chosen right Kan extension assignment preserves composition. -/
@[stacks 018C "composition law for the diagram of chosen right Kan extensions"]
theorem map_comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) :
    map L (K.map (f ≫ g)) = map L (K.map f) ≫ map L (K.map g) := sorry

end diagram

/-- The diagram formed by individually choosing a right Kan extension at every object of `K`.
No right Kan extensions away from the objects of `K` are required. -/
@[stacks 018C "diagram of individually chosen right Kan extensions"]
noncomputable def diagram (K : J ⥤ (A ⥤ C))
    [∀ j, L.HasRightKanExtension (K.obj j)] : J ⥤ (B ⥤ C) where
  obj j := L.rightKanExtension (K.obj j)
  map f := map L (K.map f)
  map_id j := diagram.map_id L K j
  map_comp f g := diagram.map_comp L K f g

namespace diagram

variable {K K' : J ⥤ (A ⥤ C)}
variable [∀ j, L.HasRightKanExtension (K.obj j)]
variable [∀ j, L.HasRightKanExtension (K'.obj j)]

/-- The componentwise maps of chosen right Kan extensions satisfy naturality over the diagram
index. -/
@[stacks 018C "naturality of a map of chosen-right-Kan-extension diagrams",
  stacks 018D "naturality of a map of chosen-right-Kan-extension pullback diagrams"]
theorem map_naturality (η : K ⟶ K') {i j : J} (f : i ⟶ j) :
    (diagram L K).map f ≫ Functor.RightKanExtension.map L (η.app j) =
      Functor.RightKanExtension.map L (η.app i) ≫ (diagram L K').map f := sorry

/-- A natural transformation of source diagrams induces the componentwise natural
transformation between their diagrams of chosen right Kan extensions. -/
@[stacks 018C "map of chosen-right-Kan-extension diagrams",
  stacks 018D "map of chosen-right-Kan-extension pullback diagrams"]
noncomputable def map (η : K ⟶ K') : diagram L K ⟶ diagram L K' where
  app j := Functor.RightKanExtension.map L (η.app j)
  naturality _ _ f := map_naturality L η f

/-- The component of the induced map of chosen-right-Kan-extension diagrams is the chosen right
Kan extension map of the corresponding source component. -/
@[simp, stacks 018C "components of a map of chosen-right-Kan-extension diagrams",
  stacks 018D "components of a map of chosen-right-Kan-extension pullback diagrams"]
theorem map_app (η : K ⟶ K') (j : J) :
    (map L η).app j = Functor.RightKanExtension.map L (η.app j) := sorry

namespace map

/-- The diagram map induced by an identity natural transformation is the identity. -/
@[simp, stacks 018C "identity map of chosen-right-Kan-extension diagrams"]
theorem id (K₁ : J ⥤ (A ⥤ C)) [∀ j, L.HasRightKanExtension (K₁.obj j)] :
    diagram.map L (𝟙 K₁) = 𝟙 (diagram L K₁) := sorry

/-- Maps of chosen-right-Kan-extension diagrams preserve composition. -/
@[stacks 018C "composition of maps of chosen-right-Kan-extension diagrams"]
theorem comp {K'' : J ⥤ (A ⥤ C)}
    [∀ j, L.HasRightKanExtension (K''.obj j)]
    (η : K ⟶ K') (θ : K' ⟶ K'') :
    diagram.map L (η ≫ θ) = diagram.map L η ≫ diagram.map L θ := sorry

end map
end diagram

namespace limit

variable (K : J ⥤ (A ⥤ C)) [HasLimit K]
variable [∀ j, L.HasRightKanExtension (K.obj j)]
variable [L.HasRightKanExtension (Limits.limit K)]

namespace cone

/-- Naturality of the projections from the right Kan extension of the source limit. -/
@[stacks 018C "naturality of right Kan extension limit projections",
  stacks 018D "naturality of right Kan extension pullback projections"]
theorem naturality {j j' : J} (f : j ⟶ j') :
    ((Functor.const J).obj (L.rightKanExtension (Limits.limit K))).map f ≫
        map L (Limits.limit.π K j') =
      map L (Limits.limit.π K j) ≫ (diagram L K).map f := sorry

end cone

/-- The canonical cone from the right Kan extension of the source limit to the diagram of
individually chosen right Kan extensions. -/
@[stacks 018C "right Kan extension limit cone",
  stacks 018D "right Kan extension pullback cone"]
noncomputable def cone : Cone (diagram L K) where
  pt := L.rightKanExtension (Limits.limit K)
  π :=
    { app := fun j ↦ map L (Limits.limit.π K j)
      naturality := fun _ _ f ↦ cone.naturality L K f }

namespace sourceCone

variable (s : Cone (diagram L K))

/-- Naturality of the cone over `K` obtained by restricting a cone over the chosen right Kan
extensions and composing with their counits. -/
@[stacks 018C "restricted cone naturality for chosen right Kan extensions",
  stacks 018D "restricted pullback cone naturality for chosen right Kan extensions"]
theorem naturality {j j' : J} (f : j ⟶ j') :
    ((Functor.const J).obj (L ⋙ s.pt)).map f ≫
        (L.whiskerLeft (s.π.app j') ≫ L.rightKanExtensionCounit (K.obj j')) =
      (L.whiskerLeft (s.π.app j) ≫ L.rightKanExtensionCounit (K.obj j)) ≫
        K.map f := sorry

end sourceCone

/-- Restrict a cone over the diagram of chosen right Kan extensions along `L` and compose its
legs with the right Kan extension counits. -/
@[stacks 018C "source cone of a chosen-right-Kan-extension cone",
  stacks 018D "source pullback cone of a chosen-right-Kan-extension cone"]
noncomputable def sourceCone (s : Cone (diagram L K)) : Cone K where
  pt := L ⋙ s.pt
  π :=
    { app := fun j ↦
        L.whiskerLeft (s.π.app j) ≫ L.rightKanExtensionCounit (K.obj j)
      naturality := fun _ _ f ↦ sourceCone.naturality L K s f }

/-- The universal lift of a cone over individually chosen right Kan extensions.  It is formed by
first lifting the restricted cone to the source limit and then using the right Kan extension
universal property. -/
@[stacks 018C "lift for the right Kan extension limit cone",
  stacks 018D "lift for the right Kan extension pullback cone"]
noncomputable def lift (s : Cone (diagram L K)) :
    s.pt ⟶ L.rightKanExtension (Limits.limit K) :=
  (L.rightKanExtension (Limits.limit K)).liftOfIsRightKanExtension
    (L.rightKanExtensionCounit (Limits.limit K)) s.pt
    (Limits.limit.lift K (sourceCone L K s))

/-- The universal lift to the right Kan extension limit cone has the prescribed components. -/
@[stacks 018C "right Kan extension limit lift on projections",
  stacks 018D "right Kan extension pullback lift on projections"]
theorem lift_fac (s : Cone (diagram L K)) (j : J) :
    lift L K s ≫ (cone L K).π.app j = s.π.app j := sorry

/-- A morphism into the right Kan extension limit cone is determined by its components. -/
@[stacks 018C "uniqueness for the right Kan extension limit cone",
  stacks 018D "uniqueness for the right Kan extension pullback cone"]
theorem lift_uniq (s : Cone (diagram L K))
    (m : s.pt ⟶ (cone L K).pt)
    (h : ∀ j, m ≫ (cone L K).π.app j = s.π.app j) :
    m = lift L K s := sorry

/-- An individually chosen right Kan extension of a source limit is a limit of the individually
chosen right Kan extensions.  The universal lift is the explicit map `limit.lift`. -/
@[stacks 018C "individually chosen right Kan extensions preserve limits",
  stacks 018D "individually chosen right Kan extensions preserve pullbacks"]
noncomputable def isLimit : IsLimit (cone L K) where
  lift := lift L K
  fac := lift_fac L K
  uniq := lift_uniq L K

/-- The explicit right Kan extension limit cone supplies a canonical limit instance for the
diagram of chosen extensions. This keeps downstream wrappers from having to rebuild a local
`HasLimit` instance for the same cone. -/
@[stacks 018C "limit instance for a diagram of chosen right Kan extensions",
  stacks 018D "pullback instance for a diagram of chosen right Kan extensions"]
noncomputable instance (priority := 100) hasLimit : HasLimit (diagram L K) :=
  HasLimit.mk ⟨cone L K, isLimit L K⟩

/-- The canonical comparison from the right Kan extension of a source limit to the chosen limit
of the individually chosen right Kan extensions. -/
@[stacks 018C "chosen right Kan extension limit comparison",
  stacks 018D "chosen right Kan extension pullback comparison"]
noncomputable def iso :
    L.rightKanExtension (Limits.limit K) ≅ Limits.limit (diagram L K) :=
  IsLimit.conePointUniqueUpToIso (isLimit L K)
    (CategoryTheory.Limits.limit.isLimit (diagram L K))

/-- The forward limit comparison followed by a projection is the map induced by the source
limit projection. -/
@[reassoc (attr := simp), stacks 018C "right Kan extension limit comparison on projections",
  stacks 018D "right Kan extension pullback comparison on projections"]
theorem iso_hom_π [HasLimit (diagram L K)] (j : J) :
    (iso L K).hom ≫ Limits.limit.π (diagram L K) j =
      map L (Limits.limit.π K j) := sorry

/-- The inverse limit comparison recovers each chosen target-limit projection. -/
@[reassoc (attr := simp), stacks 018C "inverse right Kan extension limit comparison on projections",
  stacks 018D "inverse right Kan extension pullback comparison on projections"]
theorem iso_inv_π [HasLimit (diagram L K)] (j : J) :
    (iso L K).inv ≫ map L (Limits.limit.π K j) =
      Limits.limit.π (diagram L K) j := sorry

section Naturality

variable {K₁ K₂ : J ⥤ (A ⥤ C)} [HasLimit K₁] [HasLimit K₂]
variable [∀ j, L.HasRightKanExtension (K₁.obj j)]
variable [∀ j, L.HasRightKanExtension (K₂.obj j)]
variable [L.HasRightKanExtension (Limits.limit K₁)]
variable [L.HasRightKanExtension (Limits.limit K₂)]
variable [HasLimit (diagram L K₁)] [HasLimit (diagram L K₂)]

/-- The forward right Kan extension limit comparison is natural in the source diagram. -/
@[reassoc, stacks 018C "naturality of the right Kan extension limit comparison",
  stacks 018D "naturality of the right Kan extension pullback comparison"]
theorem iso_hom_naturality (η : K₁ ⟶ K₂) :
    map L (Limits.limMap η) ≫ (iso L K₂).hom =
      (iso L K₁).hom ≫ Limits.limMap (diagram.map L η) := sorry

/-- The inverse right Kan extension limit comparison is natural in the source diagram. -/
@[reassoc, stacks 018C "naturality of the inverse right Kan extension limit comparison",
  stacks 018D "naturality of the inverse right Kan extension pullback comparison"]
theorem iso_inv_naturality (η : K₁ ⟶ K₂) :
    Limits.limMap (diagram.map L η) ≫ (iso L K₂).inv =
      (iso L K₁).inv ≫ map L (Limits.limMap η) := sorry

end Naturality

end limit

namespace prod

variable (F G : A ⥤ C) [HasBinaryProduct F G]
variable [L.HasRightKanExtension F] [L.HasRightKanExtension G]
variable [L.HasRightKanExtension (F ⨯ G)]

/-- The binary fan whose point is the chosen right Kan extension of `F ⨯ G` and whose legs
are induced by the two product projections. -/
@[stacks 018C "product cone for individually chosen right Kan extensions"]
noncomputable def cone :
    BinaryFan (L.rightKanExtension F) (L.rightKanExtension G) :=
  BinaryFan.mk
    (map L (F := F ⨯ G) (G := F) (Limits.prod.fst : F ⨯ G ⟶ F))
    (map L (F := F ⨯ G) (G := G) (Limits.prod.snd : F ⨯ G ⟶ G))

/-- The source-product morphism associated to a pair of morphisms into chosen right Kan
extensions.  Its components are obtained by restriction along `L` and the two counits. -/
@[stacks 018C "source product map for chosen right Kan extensions"]
noncomputable def sourceLift {T : B ⥤ C}
    (f : T ⟶ L.rightKanExtension F) (g : T ⟶ L.rightKanExtension G) :
    L ⋙ T ⟶ F ⨯ G :=
  Limits.prod.lift
    (L.whiskerLeft f ≫ L.rightKanExtensionCounit F)
    (L.whiskerLeft g ≫ L.rightKanExtensionCounit G)

/-- The universal lift from a pair of morphisms into individually chosen right Kan extensions
to the right Kan extension of their source product. -/
@[stacks 018C "lift into the right Kan extension of a product"]
noncomputable def lift {T : B ⥤ C}
    (f : T ⟶ L.rightKanExtension F) (g : T ⟶ L.rightKanExtension G) :
    T ⟶ L.rightKanExtension (F ⨯ G) :=
  (L.rightKanExtension (F ⨯ G)).liftOfIsRightKanExtension
    (L.rightKanExtensionCounit (F ⨯ G)) T (sourceLift L F G f g)

/-- The product lift followed by the first projection is its first prescribed component. -/
@[stacks 018C "right Kan extension product lift on the first projection"]
theorem lift_fst {T : B ⥤ C}
    (f : T ⟶ L.rightKanExtension F) (g : T ⟶ L.rightKanExtension G) :
    lift L F G f g ≫ (cone L F G).fst = f := sorry

/-- The product lift followed by the second projection is its second prescribed component. -/
@[stacks 018C "right Kan extension product lift on the second projection"]
theorem lift_snd {T : B ⥤ C}
    (f : T ⟶ L.rightKanExtension F) (g : T ⟶ L.rightKanExtension G) :
    lift L F G f g ≫ (cone L F G).snd = g := sorry

/-- A morphism to the right Kan extension of a product is determined by its two components. -/
@[stacks 018C "uniqueness of the right Kan extension product lift"]
theorem lift_uniq {T : B ⥤ C}
    (f : T ⟶ L.rightKanExtension F) (g : T ⟶ L.rightKanExtension G)
    (m : T ⟶ (cone L F G).pt)
    (h_fst : m ≫ (cone L F G).fst = f)
    (h_snd : m ≫ (cone L F G).snd = g) :
    m = lift L F G f g := sorry

/-- The right Kan extension of a source product is a product of the individually chosen right
Kan extensions.  Its lift is the explicit map `prod.lift`. -/
@[stacks 018C "individually chosen right Kan extensions preserve binary products"]
noncomputable def isLimit : IsLimit (cone L F G) :=
  BinaryFan.IsLimit.mk (cone L F G) (lift L F G)
    (lift_fst L F G) (lift_snd L F G) (lift_uniq L F G)

/-- The explicit right Kan extension product cone supplies a canonical binary-product instance for
the two chosen target extensions. -/
@[stacks 018C "binary-product instance for chosen right Kan extensions"]
noncomputable instance (priority := 100) hasBinaryProduct :
    HasBinaryProduct (L.rightKanExtension F) (L.rightKanExtension G) :=
  HasLimit.mk ⟨cone L F G, isLimit L F G⟩

/-- The canonical binary-product comparison for individually chosen right Kan extensions. -/
@[stacks 018C "binary-product comparison for chosen right Kan extensions"]
noncomputable def iso :
    L.rightKanExtension (F ⨯ G) ≅
      L.rightKanExtension F ⨯ L.rightKanExtension G :=
  IsLimit.conePointUniqueUpToIso (isLimit L F G)
    (CategoryTheory.Limits.limit.isLimit
      (Limits.pair (L.rightKanExtension F) (L.rightKanExtension G)))

/-- The hom of the product comparison followed by the first projection is the right Kan
extension map induced by the source first projection. -/
@[reassoc (attr := simp), stacks 018C "product comparison on the first projection"]
theorem iso_hom_fst
    [HasBinaryProduct (L.rightKanExtension F) (L.rightKanExtension G)] :
    (iso L F G).hom ≫ Limits.prod.fst =
      map L (Limits.prod.fst : F ⨯ G ⟶ F) := sorry

/-- The hom of the product comparison followed by the second projection is the right Kan
extension map induced by the source second projection. -/
@[reassoc (attr := simp), stacks 018C "product comparison on the second projection"]
theorem iso_hom_snd
    [HasBinaryProduct (L.rightKanExtension F) (L.rightKanExtension G)] :
    (iso L F G).hom ≫ Limits.prod.snd =
      map L (Limits.prod.snd : F ⨯ G ⟶ G) := sorry

/-- The inverse product comparison followed by the map induced by the source first projection
recovers the chosen target first projection. -/
@[reassoc (attr := simp), stacks 018C "inverse product comparison on the first projection"]
theorem iso_inv_fst
    [HasBinaryProduct (L.rightKanExtension F) (L.rightKanExtension G)] :
    (iso L F G).inv ≫ map L (Limits.prod.fst : F ⨯ G ⟶ F) =
      Limits.prod.fst := sorry

/-- The inverse product comparison followed by the map induced by the source second projection
recovers the chosen target second projection. -/
@[reassoc (attr := simp), stacks 018C "inverse product comparison on the second projection"]
theorem iso_inv_snd
    [HasBinaryProduct (L.rightKanExtension F) (L.rightKanExtension G)] :
    (iso L F G).inv ≫ map L (Limits.prod.snd : F ⨯ G ⟶ G) =
      Limits.prod.snd := sorry

end prod

namespace pullback

variable {X Y Z : A ⥤ C} (f : X ⟶ Z) (g : Y ⟶ Z)
variable [HasPullback f g]
variable [L.HasRightKanExtension X] [L.HasRightKanExtension Y]
variable [L.HasRightKanExtension Z]
variable [L.HasRightKanExtension (Limits.pullback f g)]

/-- The maps induced by the two source pullback projections satisfy the target pullback
condition. -/
@[stacks 018D "pullback condition for chosen right Kan extension maps"]
theorem condition :
    map L (Limits.pullback.fst f g) ≫ map L f =
      map L (Limits.pullback.snd f g) ≫ map L g := sorry

/-- The pullback cone whose point is the chosen right Kan extension of the source pullback. -/
@[stacks 018D "pullback cone for individually chosen right Kan extensions"]
noncomputable def cone : PullbackCone (map L f) (map L g) :=
  PullbackCone.mk
    (map L (Limits.pullback.fst f g))
    (map L (Limits.pullback.snd f g)) (condition L f g)

namespace sourceLift

/-- Restricting a pullback cone and composing with the chosen right Kan extension counits gives
a compatible pair of maps to the source cospan. -/
@[stacks 018D "source pullback condition for a chosen-right-Kan-extension cone"]
theorem condition (s : PullbackCone (map L f) (map L g)) :
    (L.whiskerLeft s.fst ≫ L.rightKanExtensionCounit X) ≫ f =
      (L.whiskerLeft s.snd ≫ L.rightKanExtensionCounit Y) ≫ g := sorry

end sourceLift

/-- The map to the source pullback obtained by restricting a pullback cone and composing its legs
with the chosen right Kan extension counits. -/
@[stacks 018D "source pullback map for chosen right Kan extensions"]
noncomputable def sourceLift (s : PullbackCone (map L f) (map L g)) :
    L ⋙ s.pt ⟶ Limits.pullback f g :=
  Limits.pullback.lift
    (L.whiskerLeft s.fst ≫ L.rightKanExtensionCounit X)
    (L.whiskerLeft s.snd ≫ L.rightKanExtensionCounit Y)
    (w := sourceLift.condition L f g s)

/-- The universal lift from a pullback cone over the chosen right Kan extensions to the right Kan
extension of the source pullback. -/
@[stacks 018D "lift into the right Kan extension of a pullback"]
noncomputable def lift (s : PullbackCone (map L f) (map L g)) :
    s.pt ⟶ L.rightKanExtension (Limits.pullback f g) :=
  (L.rightKanExtension (Limits.pullback f g)).liftOfIsRightKanExtension
    (L.rightKanExtensionCounit (Limits.pullback f g)) s.pt
    (sourceLift L f g s)

/-- The pullback lift followed by the first projection is its first prescribed component. -/
@[stacks 018D "right Kan extension pullback lift on the first projection"]
theorem lift_fst (s : PullbackCone (map L f) (map L g)) :
    lift L f g s ≫ (cone L f g).fst = s.fst := sorry

/-- The pullback lift followed by the second projection is its second prescribed component. -/
@[stacks 018D "right Kan extension pullback lift on the second projection"]
theorem lift_snd (s : PullbackCone (map L f) (map L g)) :
    lift L f g s ≫ (cone L f g).snd = s.snd := sorry

/-- A morphism to the right Kan extension of a pullback is determined by its two components. -/
@[stacks 018D "uniqueness of the right Kan extension pullback lift"]
theorem lift_uniq (s : PullbackCone (map L f) (map L g))
    (m : s.pt ⟶ (cone L f g).pt)
    (h_fst : m ≫ (cone L f g).fst = s.fst)
    (h_snd : m ≫ (cone L f g).snd = s.snd) :
    m = lift L f g s := sorry

/-- The right Kan extension of a source pullback is a pullback of the individually chosen right
Kan extensions.  Its lift is the explicit map `pullback.lift`. -/
@[stacks 018D "individually chosen right Kan extensions preserve pullbacks"]
noncomputable def isLimit : IsLimit (cone L f g) :=
  PullbackCone.IsLimit.mk (condition L f g) (lift L f g)
    (lift_fst L f g) (lift_snd L f g) (lift_uniq L f g)

/-- The explicit right Kan extension pullback cone supplies a canonical pullback instance for the
two chosen target maps. -/
@[stacks 018D "pullback instance for chosen right Kan extension maps"]
noncomputable instance (priority := 100) hasPullback :
    HasPullback (map L f) (map L g) :=
  HasLimit.mk ⟨cone L f g, isLimit L f g⟩

/-- The canonical pullback comparison for individually chosen right Kan extensions. -/
@[stacks 018D "pullback comparison for chosen right Kan extensions"]
noncomputable def iso :
    L.rightKanExtension (Limits.pullback f g) ≅
      Limits.pullback (map L f) (map L g) :=
  IsLimit.conePointUniqueUpToIso (isLimit L f g)
    (Limits.pullback.isLimit (map L f) (map L g))

/-- The hom of the pullback comparison followed by the first projection is the right Kan
extension map induced by the source first projection. -/
@[reassoc (attr := simp), stacks 018D "pullback comparison on the first projection"]
theorem iso_hom_fst [HasPullback (map L f) (map L g)] :
    (iso L f g).hom ≫ Limits.pullback.fst (map L f) (map L g) =
      map L (Limits.pullback.fst f g) := sorry

/-- The hom of the pullback comparison followed by the second projection is the right Kan
extension map induced by the source second projection. -/
@[reassoc (attr := simp), stacks 018D "pullback comparison on the second projection"]
theorem iso_hom_snd [HasPullback (map L f) (map L g)] :
    (iso L f g).hom ≫ Limits.pullback.snd (map L f) (map L g) =
      map L (Limits.pullback.snd f g) := sorry

/-- The inverse pullback comparison followed by the map induced by the source first projection
recovers the chosen target first projection. -/
@[reassoc (attr := simp), stacks 018D "inverse pullback comparison on the first projection"]
theorem iso_inv_fst [HasPullback (map L f) (map L g)] :
    (iso L f g).inv ≫ map L (Limits.pullback.fst f g) =
      Limits.pullback.fst (map L f) (map L g) := sorry

/-- The inverse pullback comparison followed by the map induced by the source second projection
recovers the chosen target second projection. -/
@[reassoc (attr := simp), stacks 018D "inverse pullback comparison on the second projection"]
theorem iso_inv_snd [HasPullback (map L f) (map L g)] :
    (iso L f g).inv ≫ map L (Limits.pullback.snd f g) =
      Limits.pullback.snd (map L f) (map L g) := sorry

end pullback

end CategoryTheory.Functor.RightKanExtension
