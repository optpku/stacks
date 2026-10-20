module

public import ReasLib.AlgebraicGeometry.Scheme.GRingStalks

/-!
# Schemes with G-ring stalks

A scheme has G-ring stalks when every structure-sheaf stalk is a G-ring.
-/

@[expose] public section

universe u

#check (AlgebraicGeometry.Scheme.HasGRingStalks : AlgebraicGeometry.Scheme.{u} → Prop)
