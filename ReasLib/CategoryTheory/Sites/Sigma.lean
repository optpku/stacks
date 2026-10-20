module

public import Mathlib.CategoryTheory.Sigma.Basic
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Sites.Continuous

@[expose] public section

universe w v u v' u'

namespace CategoryTheory.Sigma

open Opposite

variable {I : Type w} {C : I → Type u} [∀ i, Category.{v} (C i)]
variable (J : ∀ i, GrothendieckTopology (C i))

/-- A sieve on a disjoint union covers when its restriction to its component covers. -/
def coveringSieves (X : Σ i, C i) : Set (Sieve X) :=
  {S | S.functorPullback (incl X.1) ∈ J X.1 X.2}

/-- The maximal sieve restricts to a covering sieve in its component. -/
theorem top_mem_coveringSieves (X : Σ i, C i) :
    ⊤ ∈ coveringSieves J X := sorry

/-- Componentwise covering sieves are stable under pullback. -/
theorem pullback_mem_coveringSieves {X Y : Σ i, C i} {S : Sieve X}
    (f : Y ⟶ X) (hS : S ∈ coveringSieves J X) :
    S.pullback f ∈ coveringSieves J Y := sorry

/-- A sieve locally covering on a componentwise cover is itself componentwise covering. -/
theorem transitive_coveringSieves {X : Σ i, C i} {S : Sieve X}
    (hS : S ∈ coveringSieves J X) (R : Sieve X)
    (hR : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → R.pullback f ∈ coveringSieves J Y) :
    R ∈ coveringSieves J X := sorry

/-- The Grothendieck topology on a disjoint union with the given component topologies. -/
def topology : GrothendieckTopology (Σ i, C i) where
  sieves := coveringSieves J
  top_mem' := top_mem_coveringSieves J
  pullback_stable' := fun {_ _ _} f hS => pullback_mem_coveringSieves J f hS
  transitive' := fun {_ _} hS R hR => transitive_coveringSieves J hS R hR

/-- Covering in the disjoint-union topology is equivalent to covering in the component. -/
theorem mem_topology_iff {X : Σ i, C i} {S : Sieve X} :
    S ∈ topology J X ↔ S.functorPullback (incl X.1) ∈ J X.1 X.2 := sorry

/-- Each component inclusion is continuous for the disjoint-union topology. -/
instance incl_isContinuous (i : I) :
    (incl i).IsContinuous (J i) (topology J) := sorry

variable (A : Type u') [Category.{v'} A]

/-- Restriction of sheaves on a disjoint union to all its component sites. -/
def restrict : Sheaf (topology J) A ⥤ ∀ i, Sheaf (J i) A :=
  Functor.pi' fun i => (incl i).sheafPushforwardContinuous A (J i) (topology J)

variable {A}

/-- The restriction map of the componentwise glued presheaf. -/
def glueMap (F : ∀ i, Sheaf (J i) A) :
    ∀ {X Y : Σ i, C i}, (Y ⟶ X) →
      ((F X.1).obj.obj (op X.2) ⟶ (F Y.1).obj.obj (op Y.2))
  | _, _, SigmaHom.mk f => (F _).obj.map f.op

/-- Componentwise presheaf restriction preserves identity morphisms. -/
theorem glueMap_id (F : ∀ i, Sheaf (J i) A) (X : Σ i, C i) :
    glueMap J F (𝟙 X) = 𝟙 ((F X.1).obj.obj (op X.2)) := sorry

/-- Componentwise presheaf restriction reverses composition. -/
theorem glueMap_comp (F : ∀ i, Sheaf (J i) A) {X Y Z : Σ i, C i}
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    glueMap J F (g ≫ f) = glueMap J F f ≫ glueMap J F g := sorry

/-- The presheaf obtained by evaluating each supplied sheaf on its own component. -/
def gluePresheaf (F : ∀ i, Sheaf (J i) A) : (Σ i, C i)ᵒᵖ ⥤ A where
  obj X := (F X.unop.1).obj.obj (op X.unop.2)
  map f := glueMap J F f.unop
  map_id X := glueMap_id J F X.unop
  map_comp f g := glueMap_comp J F f.unop g.unop

/-- Componentwise gluing of sheaves satisfies the disjoint-union sheaf condition. -/
theorem gluePresheaf_isSheaf (F : ∀ i, Sheaf (J i) A) :
    Presheaf.IsSheaf (topology J) (gluePresheaf J F) := sorry

/-- The sheaf on the disjoint union obtained by gluing the supplied component sheaves. -/
def glueObj (F : ∀ i, Sheaf (J i) A) : Sheaf (topology J) A :=
  ⟨gluePresheaf J F, gluePresheaf_isSheaf J F⟩

/-- Component maps of a morphism of sheaf families are natural on the disjoint union. -/
theorem glueHom_naturality {F G : ∀ i, Sheaf (J i) A} (η : F ⟶ G)
    {X Y : (Σ i, C i)ᵒᵖ} (f : X ⟶ Y) :
    (gluePresheaf J F).map f ≫ (η Y.unop.1).hom.app (op Y.unop.2) =
      (η X.unop.1).hom.app (op X.unop.2) ≫ (gluePresheaf J G).map f := sorry

/-- A morphism of component sheaves induces a morphism of their glued sheaves. -/
def glueHom {F G : ∀ i, Sheaf (J i) A} (η : F ⟶ G) : glueObj J F ⟶ glueObj J G :=
  ObjectProperty.homMk
    { app := fun X => (η X.unop.1).hom.app (op X.unop.2)
      naturality := fun _ _ f => glueHom_naturality J η f }

/-- Gluing morphisms of sheaf families preserves identities. -/
theorem glue_id (F : ∀ i, Sheaf (J i) A) :
    glueHom J (𝟙 F) = 𝟙 (glueObj J F) := sorry

/-- Gluing morphisms of sheaf families preserves composition. -/
theorem glue_comp {F G H : ∀ i, Sheaf (J i) A} (η : F ⟶ G) (θ : G ⟶ H) :
    glueHom J (η ≫ θ) = glueHom J η ≫ glueHom J θ := sorry

variable (A)

/-- The functor gluing component sheaves to a sheaf on the disjoint union. -/
def glue : (∀ i, Sheaf (J i) A) ⥤ Sheaf (topology J) A where
  obj := glueObj J
  map := glueHom J
  map_id := glue_id J
  map_comp := glue_comp J

/-- Identity component maps compare a sheaf naturally with its restriction and reconstruction. -/
theorem unitApp_naturality (F : Sheaf (topology J) A)
    {X Y : (Σ i, C i)ᵒᵖ} (f : X ⟶ Y) :
    F.obj.map f ≫ 𝟙 (F.obj.obj Y) =
      𝟙 (F.obj.obj X) ≫ ((restrict J A ⋙ glue J A).obj F).obj.map f := sorry

/-- A sheaf is isomorphic to the gluing of its component restrictions by identity maps. -/
def unitApp (F : Sheaf (topology J) A) :
    F ≅ (restrict J A ⋙ glue J A).obj F :=
  (fullyFaithfulSheafToPresheaf (topology J) A).preimageIso
    (NatIso.ofComponents (fun X => Iso.refl (F.obj.obj X))
      (fun f => unitApp_naturality J A F f))

/-- The reconstruction isomorphisms are natural in sheaves on the disjoint union. -/
theorem unitIso_naturality {F G : Sheaf (topology J) A} (η : F ⟶ G) :
    η ≫ (unitApp J A G).hom =
      (unitApp J A F).hom ≫ (restrict J A ⋙ glue J A).map η := sorry

/-- The natural isomorphism from the identity to restriction followed by gluing. -/
def unitIso : 𝟭 (Sheaf (topology J) A) ≅ restrict J A ⋙ glue J A :=
  NatIso.ofComponents (unitApp J A) (fun η => unitIso_naturality J A η)

/-- Identity maps compare each restriction of a glued family naturally with its original sheaf. -/
theorem counitApp_naturality (F : ∀ i, Sheaf (J i) A) (i : I)
    {X Y : (C i)ᵒᵖ} (f : X ⟶ Y) :
    (((glue J A ⋙ restrict J A).obj F) i).obj.map f ≫ 𝟙 ((F i).obj.obj Y) =
      𝟙 ((F i).obj.obj X) ≫ (F i).obj.map f := sorry

/-- Restricting a glued family recovers the supplied sheaves by identity maps. -/
def counitApp (F : ∀ i, Sheaf (J i) A) :
    (glue J A ⋙ restrict J A).obj F ≅ F :=
  Pi.isoMk fun i => (fullyFaithfulSheafToPresheaf (J i) A).preimageIso
    (NatIso.ofComponents (fun X => Iso.refl ((F i).obj.obj X))
      (fun f => counitApp_naturality J A F i f))

/-- Component recovery isomorphisms are natural in families of sheaves. -/
theorem counitIso_naturality {F G : ∀ i, Sheaf (J i) A} (η : F ⟶ G) :
    (glue J A ⋙ restrict J A).map η ≫ (counitApp J A G).hom =
      (counitApp J A F).hom ≫ η := sorry

/-- The natural isomorphism from gluing followed by restriction to the identity. -/
def counitIso : glue J A ⋙ restrict J A ≅ 𝟭 (∀ i, Sheaf (J i) A) :=
  NatIso.ofComponents (counitApp J A) (fun η => counitIso_naturality J A η)

/-- The restriction-gluing unit and counit satisfy the triangle identity. -/
theorem sheafEquiv_triangle (F : Sheaf (topology J) A) :
    (restrict J A).map ((unitIso J A).hom.app F) ≫
      (counitIso J A).hom.app ((restrict J A).obj F) = 𝟙 ((restrict J A).obj F) := sorry

/-- Sheaves on a disjoint union of sites are equivalent to families of component sheaves. -/
def sheafEquiv : Sheaf (topology J) A ≌ ∀ i, Sheaf (J i) A where
  functor := restrict J A
  inverse := glue J A
  unitIso := unitIso J A
  counitIso := counitIso J A
  functor_unitIso_comp := sheafEquiv_triangle J A

end CategoryTheory.Sigma
