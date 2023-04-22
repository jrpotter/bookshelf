/--
Bald Eagle

`E'xy₁y₂y₃z₁z₂z₃ = x(y₁y₂y₃)(z₁z₂z₃)`
-/
def E' (x : α → β → γ)
  (y₁ : δ → ε → α) (y₂ : δ) (y₃ : ε)
  (z₁ : ζ → η → β) (z₂ : ζ) (z₃ : η) := x (y₁ y₂ y₃) (z₁ z₂ z₃)

/--
Becard

`B₃xyzw = x(y(zw))`
-/
def B₃ (x : α → ε) (y : β → α) (z : γ → β) (w : γ) := x (y (z w))

/--
Blackbird

`B₁xyzw = x(yzw)`
-/
def B₁ (x : α → ε) (y : β → γ → α) (z : β) (w : γ) := x (y z w)

/--
Bluebird

`Bxyz = x(yz)`
-/
def B (x : α → γ) (y : β → α) (z : β) := x (y z)

/--
Bunting

`B₂xyzwv = x(yzwv)`
-/
def B₂ (x : α → ζ) (y : β → γ → ε → α) (z : β) (w : γ) (v : ε) := x (y z w v)

/--
Cardinal Once Removed

`C*xyzw = xywz`
-/
def C_star (x : α → β → γ → δ) (y : α) (z : γ) (w : β) := x y w z

notation "C*" => C_star

/--
Cardinal

`Cxyz = xzy`
-/
def C (x : α → β → δ) (y : β) (z : α) := x z y

/--
Dickcissel

`D₁xyzwv = xyz(wv)`
-/
def D₁ (x : α → β → δ → ε) (y : α) (z : β) (w : γ → δ) (v : γ) := x y z (w v)

/--
Dove

`Dxyzw = xy(zw)`
-/
def D (x : α → γ → δ) (y : α) (z : β → γ) (w : β) := x y (z w)

/--
Dovekie

`D₂xyzwv = x(yz)(wv)`
-/
def D₂ (x : α → δ → ε) (y : β → α) (z : β) (w : γ → δ) (v : γ) := x (y z) (w v)

/--
Eagle

`Exyzwv = xy(zwv)`
-/
def E (x : α → δ → ε) (y : α) (z : β → γ → δ) (w : β) (v : γ) := x y (z w v)

/--
Finch Once Removed

`F*xyzw = xwzy`
-/
def F_star (x : α → β → γ → δ) (y : γ) (z : β) (w : α) := x w z y

notation "F*" => F_star

/--
Finch

`Fxyz = zyx`
-/
def F (x : α) (y : β) (z : β → α → γ) := z y x

/--
Goldfinch

`Gxyzw = xw(yz)`
-/
def G (x : α → γ → δ) (y : β → γ) (z : β) (w : α) := x w (y z)

/--
Hummingbird

`Hxyz = xyzy`
-/
def H (x : α → β → α → γ) (y : α) (z : β) := x y z y

/--
Identity Bird

`Ix = x`
-/
def I (x : α) : α := x

/--
Kestrel

`Kxy = x`
-/
def K (x : α) (_ : β) := x

/--
Owl

`Oxy = y(xy)`
-/
def O (x : (α → β) → α) (y : α → β) := y (x y)

/--
Phoenix

`Φxyzw = x(yw)(zw)`
-/
def Φ (x : β → γ → δ) (y : α → β) (z : α → γ) (w : α) := x (y w) (z w)

/--
Psi Bird

`Ψxyzw = x(yz)(yw)`
-/
def Ψ (x : α → α → γ) (y : β → α) (z : β) (w : β) := x (y z) (y w)

/--
Quacky Bird

`Q₄xyz = z(yx)`
-/
def Q₄ (x : α) (y : α → β) (z : β → γ) := z (y x)

/--
Queer Bird

`Qxyz = y(xz)`
-/
def Q (x : α → β) (y : β → γ) (z : α) := y (x z)

/--
Quirky Bird

`Q₃xyz = z(xy)`
-/
def Q₃ (x : α → β) (y : α) (z : β → γ) := z (x y)

/--
Quixotic Bird

`Q₁xyz = x(zy)`
-/
def Q₁ (x : α → γ) (y : β) (z : β → α) := x (z y)

/--
Quizzical Bird

`Q₂xyz = y(zx)`
-/
def Q₂ (x : α) (y : β → γ) (z : α → β) := y (z x)

/--
Robin Once Removed

`R*xyzw = xzwy`
-/
def R_star (x : α → β → γ → δ) (y : γ) (z : α) (w : β) := x z w y

notation "R*" => R_star

/--
Robin

`Rxyz = yzx`
-/
def R (x : α) (y : β → α → γ) (z : β) := y z x

/--
Starling

`Sxyz = xz(yz)`
-/
def S (x : α → β → γ) (y : α → β) (z : α) := x z (y z)

/--
Thrush

`Txy = yx`
-/
def T (x : α) (y : α → β) := y x

/--
Vireo Once Removed

`V*xyzw = xwyz`
-/
def V_star (x : α → β → γ → δ) (y : β) (z : γ) (w : α) := x w y z

notation "V*" => V_star

/--
Vireo

`Vxyz = zxy`
-/
def V (x : α) (y : β) (z : α → β → γ) := z x y
