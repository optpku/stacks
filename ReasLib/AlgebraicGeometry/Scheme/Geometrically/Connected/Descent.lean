module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Closeds.Descent

/-!
# Descent of connectedness along a Galois field extension

This leaf owns connectedness descent for schemes over a field.  The maps to
`Spec k` are explicit, so the API is independent of a chosen `Over` instance.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

namespace AlgebraicGeometry

namespace GeometricallyConnected.Galois.ConnectedSource

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]

/-- Connectedness of the source after a Galois extension and of the target before base change imply connectedness of the target after base change. -/
theorem targetBaseChange
    {T X : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (x : X ⟶ Spec (CommRingCat.of k))
    (f : T ⟶ X) (h_over : f ≫ x = t)
    (hTK : ConnectedSpace (FieldExtension.baseChange k K t))
    (hX : ConnectedSpace X) :
    ConnectedSpace (FieldExtension.baseChange k K x) := sorry

/-- Connectedness of the source after a Galois extension and disconnectedness of the target after base change imply that the target was disconnected. -/
theorem not_target
    {T X : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (x : X ⟶ Spec (CommRingCat.of k))
    (f : T ⟶ X) (h_over : f ≫ x = t)
    (hTK : ConnectedSpace (FieldExtension.baseChange k K t))
    (hXK : ¬ ConnectedSpace (FieldExtension.baseChange k K x)) :
    ¬ ConnectedSpace X := sorry

end

end GeometricallyConnected.Galois.ConnectedSource

namespace GeometricallyConnected.Descent

section

variable {k : Type u} [Field k]

/-- A geometrically connected source over a field forces a connected target to be geometrically connected. -/
theorem of_connectedTarget
    {T X : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (x : X ⟶ Spec (CommRingCat.of k))
    (f : T ⟶ X) (h_over : f ≫ x = t)
    (hT : GeometricallyConnected t)
    (hX : ConnectedSpace X) :
    GeometricallyConnected x := sorry

end

end GeometricallyConnected.Descent

end AlgebraicGeometry
