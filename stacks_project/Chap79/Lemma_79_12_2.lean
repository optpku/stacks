module

public import stacks_project.Chap79.Lemma_79_12_2_FinitePart
public import stacks_project.Chap79.Lemma_79_12_2_Map

/-!
# Canonical injectivity of finite-part sheaves along open immersions
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 79.12.2: Let `S` be a scheme. For a commutative triangle of algebraic spaces
over `S` with `j : X' ⟶ X` an open immersion over `Y`, the canonical map of fppf sheaves
`finitePartOpenMap j hcomm : finitePartSheaf f' ⟶ finitePartSheaf f` is a monomorphism. -/
@[stacks 04PF, instance]
instance instMono_finitePartOpenMap {S : Scheme.{u}} {X' X Y : AlgebraicSpace S}
    {f' : X' ⟶ Y} {f : X ⟶ Y} (j : X' ⟶ X) [IsOpenImmersion j]
    (hcomm : j ≫ f = f') : Mono (finitePartOpenMap j hcomm) := sorry

/-- The components of `finitePartOpenMap j hcomm` are injective on sections. -/
theorem finitePartOpenMap_injective {S : Scheme.{u}} {X' X Y : AlgebraicSpace S}
    {f' : X' ⟶ Y} {f : X ⟶ Y} (j : X' ⟶ X) [IsOpenImmersion j]
    (hcomm : j ≫ f = f') (T : (Over S)ᵒᵖ) :
    Function.Injective fun (p : FinitePart.Point f' T.unop) ↦
      FinitePart.Point.map j hcomm p := sorry

end AlgebraicGeometry.AlgebraicSpace
