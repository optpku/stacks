module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.Immersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 70.5.12 (1): a closed immersion into the limit descends to every sufficiently large
stage under the stated quasi-compactness and finite-type hypotheses. -/
@[stacks 0828] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.exists_eventually_isClosedImmersion_to_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {B Y : AlgebraicSpace S}
      (D : OrderDual I ⥤ AlgebraicSpace S)
      (t : D ⟶ (Functor.const (OrderDual I)).obj B)
      (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ B)
      (hπ : c.π ≫ t = (Functor.const _).map σlim)
      [∀ i : I, IsQuasiCompact (D.obj i)]
      [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
      (f : Y ⟶ c.pt) (g : Y ⟶ B) [AlgebraicSpace.IsClosedImmersion f]
      [AlgebraicSpace.LocallyOfFiniteType g] (hfg : f ≫ σlim = g),
      ∃ i : I, ∀ ⦃i' : I⦄, i ≤ i' → AlgebraicSpace.IsClosedImmersion (f ≫ c.π.app i'))

/- Lemma 70.5.12 (2): an immersion into the limit descends to every sufficiently large stage
under the stated quasi-separatedness, quasi-compactness, and finite-type hypotheses. -/
@[stacks 0828] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.exists_eventually_isImmersion_to_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {B Y : AlgebraicSpace S}
      (D : OrderDual I ⥤ AlgebraicSpace S)
      (t : D ⟶ (Functor.const (OrderDual I)).obj B)
      (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ B)
      (hπ : c.π ≫ t = (Functor.const _).map σlim)
      [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
      [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
      [IsQuasiCompact Y] (f : Y ⟶ c.pt) (g : Y ⟶ B)
      [AlgebraicSpace.IsImmersion f] [AlgebraicSpace.LocallyOfFiniteType g]
      (hfg : f ≫ σlim = g),
      ∃ i : I, ∀ ⦃i' : I⦄, i ≤ i' → AlgebraicSpace.IsImmersion (f ≫ c.π.app i'))

/- Lemma 70.5.12 (3): an isomorphism to the limit descends to every sufficiently large stage
under the stated quasi-compactness, finite-type, closed-transition, and finite-presentation
hypotheses. -/
@[stacks 0828] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.exists_eventually_isIso_to_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {B Y : AlgebraicSpace S}
      (D : OrderDual I ⥤ AlgebraicSpace S)
      (t : D ⟶ (Functor.const (OrderDual I)).obj B)
      (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ B)
      (hπ : c.π ≫ t = (Functor.const _).map σlim)
      [∀ i : I, IsQuasiCompact (D.obj i)]
      [∀ i : I, AlgebraicSpace.LocallyOfFiniteType (t.app i)]
      [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
      [∀ {i i' : I} (hii' : i ≤ i'), AlgebraicSpace.IsClosedImmersion (D.map (homOfLE hii'))]
      (f : Y ⟶ c.pt) (g : Y ⟶ B) [IsIso f]
      [AlgebraicSpace.LocallyOfFinitePresentation g] (hfg : f ≫ σlim = g),
      ∃ i : I, ∀ ⦃i' : I⦄, i ≤ i' → IsIso (f ≫ c.π.app i'))

/- Lemma 70.5.12 (4): a monomorphism into the limit descends to every sufficiently large stage
under the stated quasi-separatedness, quasi-compactness, and finite-type hypotheses. -/
@[stacks 0828] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.exists_eventually_mono_to_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {B Y : AlgebraicSpace S}
      (D : OrderDual I ⥤ AlgebraicSpace S)
      (t : D ⟶ (Functor.const (OrderDual I)).obj B)
      (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ B)
      (hπ : c.π ≫ t = (Functor.const _).map σlim)
      [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
      [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
      [IsQuasiCompact Y] (f : Y ⟶ c.pt) (g : Y ⟶ B) [Mono f]
      [AlgebraicSpace.LocallyOfFiniteType g] (hfg : f ≫ σlim = g),
      ∃ i : I, ∀ ⦃i' : I⦄, i ≤ i' → Mono (f ≫ c.π.app i'))
