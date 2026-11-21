import Std
set_option maxHeartbeats 4000000
namespace Kaprekar
abbrev P := Nat × Nat
def dist (a b : Nat) := a-b+(b-a)
def f (b t : Nat) := dist t (b-t)
def pair (x y : Nat) : P := (max x y,min x y)
def G (b : Nat) (p : P) := 0<p.2 ∧ p.2<p.1 ∧ p.1<b ∧ p.1+p.2≠b
def step (b : Nat) (p : P) := pair (f b p.1) (f b p.2)
-- Actual four digits, least significant first.
def enc (b a c d e : Nat) := a+b*(c+b*(d+b*e))
def digits (b n : Nat) := (n%b,n/b%b,n/b/b%b,n/b/b/b%b)
-- Sort two pairs, then select the two middle order statistics.
def gaps (a c d e : Nat) : P :=
  let l := min a c
  let u := max a c
  let v := min d e
  let z := max d e
  (max u z - min l v, dist (max l v) (min u z))
def pars (b n : Nat) : P :=
  let (a,c,d,e) := digits b n
  gaps a c d e
-- Difference of descending and ascending digit values in terms of outer and inner gaps.
def val (b : Nat) (p : P) := (b-1)*((b*b+b+1)*p.1+b*p.2)
def K (b n : Nat) := val b (pars b n)
theorem subtractSorted (b a c d e : Nat) (hb : 1≤b) (h1 : a≤c) (h2 : c≤d) (h3 : d≤e) :
 enc b a c d e - enc b e d c a = val b (e-a,d-c) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h1
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le h2
  obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le h3
  cases b with
  | zero => omega
  | succ b =>
    have hh : a+k+j+i-a=k+j+i := by omega
    simp only [hh,val,enc,Nat.succ_sub_one,Nat.add_sub_cancel_left, Nat.add_sub_cancel, Nat.succ_eq_add_one]
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one] <;> simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    omega
theorem decode (b a c d e : Nat) (h : a<b ∧ c<b ∧ d<b ∧ e<b) :
 digits b (enc b a c d e) = (a,c,d,e) := by
  have hb : 0<b := by omega
  simp [digits,enc,Nat.add_mul_div_left, Nat.add_mul_mod_self_left, Nat.div_eq_of_lt,
    Nat.mod_eq_of_lt,h.1,h.2.1,h.2.2.1,h.2.2.2,hb]
theorem rep (b x y : Nat) (h : G b (x,y)) :
 val b (x,y) = enc b (b-x) (b-1-y) (y-1) x := by
  simp [G] at h
  obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le (show 1≤y by omega)
  obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le (show y+1≤x by omega)
  obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le (show x+1≤b by omega)
  have e1 : b-x=1+z := by omega
  have e2 : b-1-y=1+v+z := by omega
  have e3 : y-1=u := by omega
  have e4 : b-1=x+z := by omega
  rw [e1,e2,e3]; simp only [val,enc,e4]
  rw [hz,hv,hu]
  simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one] <;> simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  omega
theorem A (b : Nat) (p : P) (h : G b p) : pars b (val b p) = step b p := by
  obtain ⟨x,y⟩ := p
  rw [rep b x y h]
  simp [G] at h
  unfold pars
  rw [decode _ _ _ _ _ (by omega)]
  simp [gaps,step,pair,f,dist,Nat.max_def,Nat.min_def]
  constructor <;> (repeat' split <;> try omega) <;> omega
def scale (m : Nat) (p : P) : P := (m*p.1,m*p.2)
theorem scaledG {b m : Nat} {p : P} (hm : 0<m) (h : G b p) : G (m*b) (scale m p) := by
  obtain ⟨a,c,d,e⟩ := h
  exact ⟨Nat.mul_pos hm a,Nat.mul_lt_mul_of_pos_left c hm,Nat.mul_lt_mul_of_pos_left d hm,
    by simpa [scale,←Nat.mul_add,hm] using (show m*(p.1+p.2)≠m*b from fun he => e (Nat.eq_of_mul_eq_mul_left hm he))⟩
theorem B (b m : Nat) (p : P) : step (m*b) (scale m p) = scale m (step b p) := by
  simp [step,scale,pair,f,dist,←Nat.mul_sub,←Nat.mul_add]
def oddIn (b t : Nat) := t<b ∧ t%2=1
theorem C {b t : Nat} (hb : b%2=1) (ht : oddIn b t) : oddIn b (f b t) := by
  unfold oddIn at *; unfold f dist; constructor <;> omega
theorem D {b x y : Nat} (hb : b%2=1) (hx : oddIn b x) (hy : oddIn b y)
    (eq : f b x=f b y) : x=y := by
  unfold oddIn at *; unfold f dist at eq; omega
def it {α : Type} (g : α → α) (n : Nat) (x : α) := match n with
  | 0 => x
  | n+1 => g (it g n x)
theorem itAdd {α : Type} (g : α → α) (x : α) (i j : Nat) : it g (i+j) x=it g j (it g i x) := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg g ih
theorem repeatBound (N : Nat) (s : Nat → Nat) (h : ∀ i, s i<N) : ∃ i j, i<j ∧ s i=s j := by
  induction N generalizing s with
  | zero => have := h 0; omega
  | succ n ih =>
    by_cases ex : ∃ i, s i=n
    · obtain ⟨i,hi⟩ := ex
      by_cases again : ∃ j, i<j ∧ s j=n
      · obtain ⟨j,hj,eq⟩ := again; exact ⟨i,j,hj,hi.trans eq.symm⟩
      · obtain ⟨u,v,lt,eq⟩ := ih (fun k => s (i+1+k)) (by
          intro k; change s (i+1+k)<n; have := h (i+1+k); have ne : s (i+1+k)≠n := fun e => again ⟨_,by omega,e⟩; omega)
        exact ⟨_,_,by omega,eq⟩
    · exact ih s (by intro k; have := h k; have ne : s k≠n := fun e => ex ⟨_,e⟩; omega)
def adj (b x y : Nat) := f b x=y ∨ f b y=x
theorem adjNext {b x y : Nat} (hb : b%2=1) (hx : oddIn b x) (hy : oddIn b y) :
 adj b (f b x) (f b y) ↔ adj b x y := by
  constructor
  · exact fun h => h.elim (fun e => Or.inl (D hb (C hb hx) hy e)) (fun e => Or.inr (D hb (C hb hy) hx e))
  · exact fun h => h.elim (fun e => Or.inl (congrArg (f b) e)) (fun e => Or.inr (congrArg (f b) e))
theorem pairG {b x y : Nat} (hb : b%2=1) (hx : oddIn b x) (hy : oddIn b y) (hne : x≠y) :
 G b (pair x y) := by
  unfold oddIn at *; simp [G,pair,Nat.max_def,Nat.min_def]; split <;> omega
theorem stepPair (b x y : Nat) : step b (pair x y) = pair (f b x) (f b y) := by
  by_cases h : x≤y
  · simp [step,pair,Nat.max_eq_right h,Nat.min_eq_left h,Nat.max_comm,Nat.min_comm]
  · have h' : y≤x := by omega
    simp [step,pair,Nat.max_eq_left h',Nat.min_eq_right h']
def orderedAdj (b : Nat) (p : P) := adj b p.1 p.2
theorem pairAdj (b x y : Nat) : orderedAdj b (pair x y) ↔ adj b x y := by
  simp [orderedAdj,pair,adj,Nat.max_def,Nat.min_def]; split <;> simp_all [or_comm]
def mark (b m n : Nat) := ∃ p, pars (m*b) n=scale m p ∧ orderedAdj b p
theorem markEq {b m n : Nat} {p : P} (hm : 0<m) (hp : pars (m*b) n=scale m p) :
 mark b m n ↔ orderedAdj b p := by
  constructor
  · rintro ⟨q,hq,h⟩
    have he := hq.symm.trans hp
    have he' : q=p := Prod.ext (Nat.eq_of_mul_eq_mul_left hm (congrArg Prod.fst he))
      (Nat.eq_of_mul_eq_mul_left hm (congrArg Prod.snd he))
    exact he' ▸ h
  · exact fun h => ⟨_,hp,h⟩
theorem build {b m x y : Nat} (hb : b%2=1) (hm : 0<m)
    (hx : oddIn b x) (hy : oddIn b y) (hne : x≠y) :
 ∃ n period, 0<period ∧ it (K (m*b)) period n=n ∧
    (∀ i, mark b m (it (K (m*b)) i n) ↔ adj b x y) ∧ 0<n ∧ n<(m*b)^4 := by
  let X i := it (f b) i x
  let Y i := it (f b) i y
  have good (i) : oddIn b (X i) ∧ oddIn b (Y i) ∧ X i≠Y i ∧ (adj b (X i) (Y i) ↔ adj b x y) := by
    induction i with
    | zero => exact ⟨hx,hy,hne,Iff.rfl⟩
    | succ i ih => exact ⟨C hb ih.1,C hb ih.2.1,fun h => ih.2.2.1 (D hb ih.1 ih.2.1 h),
        (adjNext hb ih.1 ih.2.1).trans ih.2.2.2⟩
  let p i := pair (X i) (Y i)
  let q i := scale m (p i)
  let s i := val (m*b) (q i)
  have reg i : G (m*b) (q i) := scaledG hm (pairG hb (good i).1 (good i).2.1 (good i).2.2.1)
  have parsS i : pars (m*b) (s i)=q (i+1) :=
    (A _ _ (reg i)).trans ((B _ _ _).trans (congrArg (scale m) (stepPair _ _ _)))
  have orbit (i j) : it (K (m*b)) j (s i)=s (i+j) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      change K _ (it _ j _)=_
      rw [ih]; exact congrArg (val _) (parsS _)
  have bound i : 0<s i ∧ s i<(m*b)^4 := by
    let B := m*b
    let a := (q i).1
    let c := (q i).2
    have hg : 0<c ∧ c<a ∧ a<B := ⟨(reg i).1,(reg i).2.1,(reg i).2.2.1⟩
    change 0<val B (a,c) ∧ val B (a,c)<B^4
    rw [rep B a c (reg i)]
    have hor (u v d : Nat) (hu : u<B) (hv : v<d) : u+B*v<B*d := by
      have l := Nat.mul_le_mul_left B (show v+1≤d by omega)
      rw [Nat.mul_add,Nat.mul_one] at l; omega
    constructor
    · unfold enc; omega
    · simpa [enc,Nat.pow_succ,Nat.mul_comm] using hor (B-a) _ (B^3) (by omega)
        (show B-1-c+B*(c-1+B*a)<B^3 from by
          simpa [Nat.pow_succ,Nat.mul_comm] using hor (B-1-c) _ (B^2) (by omega)
            (show c-1+B*a<B^2 from by simpa [Nat.pow_succ,Nat.mul_comm] using hor (c-1) a B (by omega) hg.2.2))
  obtain ⟨i,j,hlt,he⟩ := repeatBound _ s (fun i => (bound i).2)
  refine ⟨s i,j-i,by omega,?_,?_,bound i⟩
  · rw [orbit,show i+(j-i)=j by omega]; exact he.symm
  · intro k
    rw [orbit]
    exact (markEq hm (parsS _)).trans ((pairAdj _ _ _).trans (good _).2.2.2)
theorem twoCycles {b w : Nat} (hw : w%2=1) (h9 : 9≤w) (hb : 0<b) (hd : w∣b) :
 ∃ n v r t, 0<n ∧ n<b^4 ∧ 0<v ∧ v<b^4 ∧ 0<r ∧ 0<t ∧
 it (K b) r n=n ∧ it (K b) t v=v ∧ ∀ i j, it (K b) i n≠it (K b) j v := by
  obtain ⟨m,rfl⟩ := hd
  rw [Nat.mul_comm w m] at *
  have hm : 0<m := Nat.pos_of_mul_pos_right hb
  have h1 : oddIn w 1 := ⟨by omega,rfl⟩
  have h3 : oddIn w 3 := ⟨by omega,rfl⟩
  have hf : f w 1=w-2 := by unfold f dist; omega
  have hadj : adj w 1 (f w 1) := Or.inl rfl
  have hno : ¬adj w 1 3 := by unfold adj f dist; omega
  obtain ⟨n,r,hr,hn,ha,hpos,hlim⟩ := build hw hm h1 (C hw h1) (by rw [hf]; omega)
  obtain ⟨v,t,ht,hv,hc,vpos,vlim⟩ := build hw hm h1 h3 (by decide)
  refine ⟨n,v,r,t,hpos,hlim,vpos,vlim,hr,ht,hn,hv,?_⟩
  intro i j eq
  exact hno ((hc j).mp (eq ▸ (ha i).mpr hadj))
#print axioms twoCycles
#print axioms subtractSorted
#print axioms A
end Kaprekar

namespace Kaprekar
abbrev Quad := Nat × Nat × Nat × Nat
def sorted (a c d e : Nat) : Quad :=
  let l := min a c
  let u := max a c
  let v := min d e
  let z := max d e
  let j := max l v
  let k := min u z
  (min l v,min j k,max j k,max u z)
def ordered (q : Quad) := q.1≤q.2.1 ∧ q.2.1≤q.2.2.1 ∧ q.2.2.1≤q.2.2.2
theorem sortedOrder (a c d e : Nat) : ordered (sorted a c d e) := by
  simp [ordered,sorted,Nat.min_def,Nat.max_def]
  repeat' split <;> try omega
def cnt (t x : Nat) := if t=x then 1 else 0
theorem compareCount (t x y : Nat) :
 cnt t (min x y)+cnt t (max x y)=cnt t x+cnt t y := by
  simp [Nat.min_def,Nat.max_def]; split <;> omega
theorem sortedMultiplicity (t a c d e : Nat) :
 let q := sorted a c d e
 cnt t q.1+cnt t q.2.1+cnt t q.2.2.1+cnt t q.2.2.2=cnt t a+cnt t c+cnt t d+cnt t e := by
  unfold sorted; dsimp only
  have h1 := compareCount t a c
  have h2 := compareCount t d e
  have h3 := compareCount t (min a c) (min d e)
  have h4 := compareCount t (max a c) (max d e)
  have h5 := compareCount t (max (min a c) (min d e)) (min (max a c) (max d e))
  omega
def actual (b n : Nat) :=
  let (a,c,d,e) := digits b n
  let (u,v,x,y) := sorted a c d e
  enc b u v x y - enc b y x v u
theorem agrees (b n : Nat) (hb : 1≤b) : actual b n=K b n := by
  unfold actual K pars
  obtain ⟨a,c,d,e⟩ := digits b n
  have h := sortedOrder a c d e
  dsimp only
  rw [subtractSorted _ _ _ _ _ hb h.1 h.2.1 h.2.2]
  congr 2
  simp [sorted,gaps,dist,Nat.min_def,Nat.max_def]
  repeat' split <;> try omega
theorem certified {b w : Nat} (hw : w%2=1) (h9 : 9≤w) (hb : 0<b) (hd : w∣b) :
 ∃ n v r t, 0<n ∧ n<b^4 ∧ 0<v ∧ v<b^4 ∧ 0<r ∧ 0<t ∧
 it (actual b) r n=n ∧ it (actual b) t v=v ∧ ∀ i j, it (actual b) i n≠it (actual b) j v := by
  rw [show actual b=K b from funext (fun n => agrees b n hb)]
  exact twoCycles hw h9 hb hd
#print axioms certified
#print axioms sortedMultiplicity
example : ∃ w, w%2=1 ∧ 9≤w ∧ w∣18 := ⟨9,by decide⟩
end Kaprekar
namespace Kaprekar
theorem oddPermutation {b : Nat} (hb : b%2=1) :
 (∀ t, oddIn b t → oddIn b (f b t)) ∧
 (∀ x y, oddIn b x → oddIn b y → f b x=f b y → x=y) ∧
 (∀ y, oddIn b y → ∃ x, oddIn b x ∧ f b x=y) := by
  refine ⟨fun _ => C hb,fun _ _ => D hb,?_⟩
  intro y hy
  unfold oddIn at *
  let z := (b-y)/2
  by_cases hz : z%2=1
  · refine ⟨z,?_,?_⟩ <;> unfold z at * <;> first | (unfold f dist; omega) | (constructor <;> omega)
  · refine ⟨b-z,?_,?_⟩ <;> unfold z at * <;> first | (unfold f dist; omega) | (constructor <;> omega)
theorem regularInvariant {b : Nat} (hb : b%2=1) {p : P} (h : G b p) :
 G b (step b p) ∧ oddIn b (step b p).1 ∧ oddIn b (step b p).2 := by
  obtain ⟨x,y⟩ := p
  simp [G] at h
  have hx : oddIn b (f b x) := by unfold oddIn f dist; constructor <;> omega
  have hy : oddIn b (f b y) := by unfold oddIn f dist; constructor <;> omega
  have ne : f b x≠f b y := by unfold f dist; omega
  refine ⟨pairG hb hx hy ne,?_⟩
  simp [step,pair,Nat.min_def,Nat.max_def]; split <;> simp_all
#print axioms oddPermutation
#print axioms regularInvariant
end Kaprekar
namespace Kaprekar
-- A generic form of E, indexing an arbitrary n-element set by Fin n.
def edgeEq {α : Type} (a b c d : α) := (a=c ∧ b=d) ∨ (a=d ∧ b=c)
theorem finitePeriod {n : Nat} (g : Fin n → Fin n) (inj : ∀ {x y}, g x=g y → x=y) (x : Fin n) :
 ∃ r, 0<r ∧ it g r x=x := by
  obtain ⟨i,j,lt,eq⟩ := repeatBound n (fun k => (it g k x).val) (fun k => (it g k x).isLt)
  have cancel k : ∀ a b, it g k a=it g k b → a=b := by
    induction k with
    | zero => exact fun _ _ h => h
    | succ k ih => exact fun a b h => ih a b (inj h)
  refine ⟨j-i,by omega,cancel i _ _ ?_⟩
  rw [←itAdd,show j-i+i=j by omega]; exact Fin.ext eq.symm
theorem E {n : Nat} (hn : 4≤n) (g : Fin n → Fin n) (inj : ∀ {x y}, g x=g y → x=y) :
 ∃ a b c d : Fin n, a≠b ∧ c≠d ∧ ∀ i j,
 ¬edgeEq (it g i a) (it g i b) (it g j c) (it g j d) := by
  let u : Fin n := ⟨0,by omega⟩
  let v : Fin n := ⟨1,by omega⟩
  let w : Fin n := ⟨2,by omega⟩
  let z : Fin n := ⟨3,by omega⟩
  by_cases iden : ∀ x, g x=x
  · have h k x : it g k x=x := by induction k with
                                   | zero => rfl
                                   | succ k ih => exact (iden _).trans ih
    refine ⟨u,v,u,w,by intro e; have := congrArg Fin.val e; contradiction,
      by intro e; have := congrArg Fin.val e; contradiction,?_⟩
    intro i j; simp [h,edgeEq,u,v,w]
  · have moved : ∃ a, g a≠a := Classical.byContradiction (fun h => iden (fun x =>
        Classical.byContradiction (fun ne => h ⟨x,ne⟩)))
    obtain ⟨a,ha⟩ := moved
    let adjG (x y : Fin n) := g x=y ∨ g y=x
    have pick : ∃ d, d≠a ∧ ¬adjG a d := by
      obtain ⟨r,hr,per⟩ := finitePeriod g @inj a
      let prev := it g (r-1) a
      have pre : g prev=a := by
        change it g (r-1+1) a=a; rwa [show r-1+1=r by omega]
      have exc (d : Fin n) (h : ¬(d≠a ∧ ¬adjG a d)) :
          d.val=a.val ∨ d.val=(g a).val ∨ d.val=prev.val := by
        by_cases e : d=a
        · exact Or.inl (congrArg Fin.val e)
        · have had : adjG a d := Classical.byContradiction (fun no => h ⟨e,no⟩)
          exact had.elim (fun he => Or.inr (Or.inl (congrArg Fin.val he.symm)))
            (fun he => Or.inr (Or.inr (congrArg Fin.val (inj (he.trans pre.symm)))))
      apply Classical.byContradiction
      intro no
      have bad d := exc d (fun e => no ⟨d,e⟩)
      have h0 := bad u; have h1 := bad v; have h2 := bad w; have h3 := bad z
      simp only [u,v,w,z] at h0 h1 h2 h3; omega
    obtain ⟨d,hd,neg⟩ := pick
    have inv k x y : adjG (it g k x) (it g k y) ↔ adjG x y := by
      induction k with
      | zero => rfl
      | succ k ih =>
        apply Iff.trans _ ih
        exact ⟨fun h => h.elim (fun e => Or.inl (inj e)) (fun e => Or.inr (inj e)),
          fun h => h.elim (fun e => Or.inl (congrArg g e)) (fun e => Or.inr (congrArg g e))⟩
    refine ⟨a,g a,a,d,Ne.symm ha,Ne.symm hd,?_⟩
    intro i j h
    have yes := (inv i a (g a)).mpr (Or.inl rfl)
    apply neg ∘ (inv j a d).mp
    rcases h with ⟨l,r⟩ | ⟨l,r⟩
    · rwa [l,r] at yes
    · rw [l,r] at yes; exact yes.elim Or.inr Or.inl
#print axioms E
#print axioms finitePeriod
end Kaprekar
#print axioms Kaprekar.B
#print axioms Kaprekar.scaledG
#print axioms Kaprekar.agrees
