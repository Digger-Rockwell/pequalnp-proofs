import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_500_aux

open Turing PEqualNP.Search PEqualNP.Library

private def incBits : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: incBits bs

private theorem incBits_bits (n : ℕ) : incBits n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [incBits]
  | bit b n h ih =>
    cases b with
    | false =>
      have hn : n ≠ 0 := fun h0 => by simp [h0] at h
      have e1 : Nat.bit false n = 2 * n := by simp [Nat.bit]
      rw [e1, Nat.bit0_bits n hn, incBits, Nat.bit1_bits]
    | true =>
      have e1 : Nat.bit true n = 2 * n + 1 := by simp [Nat.bit]
      have e2 : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
      rw [e1, Nat.bit1_bits, incBits, ih, e2, Nat.bit0_bits (n + 1) (Nat.succ_ne_zero n)]

private theorem bits_injective : Function.Injective Nat.bits := by
  intro m
  induction m using Nat.binaryRec' with
  | zero =>
    intro n h
    induction n using Nat.binaryRec' with
    | zero => rfl
    | bit b n hn _ =>
      rw [Nat.zero_bits, Nat.bits_append_bit n b hn] at h
      exact absurd h (by simp)
  | bit b₁ m hm ih =>
    intro n h
    induction n using Nat.binaryRec' with
    | zero =>
      rw [Nat.zero_bits, Nat.bits_append_bit m b₁ hm] at h
      exact absurd h (by simp)
    | bit b₂ n hn _ =>
      rw [Nat.bits_append_bit m b₁ hm, Nat.bits_append_bit n b₂ hn] at h
      injection h with hb htl
      rw [hb, ih htl]

private theorem bits_length_le (n : ℕ) : n.bits.length ≤ n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h, List.length_cons]
    cases b with
    | false =>
      have hn : n ≠ 0 := fun h0 => by simp [h0] at h
      simp [Nat.bit]
      omega
    | true =>
      simp [Nat.bit]
      omega

private def tokLit (l : Literal) : List (Bool × Bool) :=
  (true, l.2) :: (l.1.bits.map fun d => (true, d)) ++ [(false, true)]

private def tokOpt : Option Literal → List (Bool × Bool)
  | some l => tokLit l
  | none => [(false, false)]

private def flatTokens (φ : CNF) : List (Option Literal) :=
  φ.flatMap (fun c => c.map some ++ [none])

private def tokToBits (ts : List (Bool × Bool)) : List Bool :=
  ts.flatMap (fun p => [p.1, p.2])

private def reindexVar (φ : CNF) (v : ℕ) : ℕ :=
  (flatTokens φ).findIdx (fun o => o.any (fun l' => l'.1 == v))

private def reindexCNF (φ : CNF) : CNF :=
  φ.map (fun c => c.map (fun l => (reindexVar φ l.1, l.2)))

private theorem tokToBits_append (a b : List (Bool × Bool)) :
    tokToBits (a ++ b) = tokToBits a ++ tokToBits b := by
  simp [tokToBits]

private theorem tokToBits_tokLit (l : Literal) :
    tokToBits (tokLit l) = encodeLiteral l := by
  unfold tokToBits tokLit encodeLiteral
  simp [List.flatMap_map]

private theorem tokToBits_cons (a b : Bool) (ts : List (Bool × Bool)) :
    tokToBits ((a, b) :: ts) = a :: b :: tokToBits ts := rfl

private theorem tokToBits_tokOpt_clause (c : Clause) :
    tokToBits ((c.map some ++ [none]).flatMap tokOpt) = encodeClause c := by
  unfold encodeClause
  induction c with
  | nil => simp [tokOpt, tokToBits]
  | cons l c ih =>
    simp only [List.map_cons, List.cons_append, List.flatMap_cons, tokToBits_append, tokOpt,
      tokToBits_tokLit]
    rw [ih, List.append_assoc]

private theorem tokToBits_flatTokens (φ : CNF) :
    tokToBits ((flatTokens φ).flatMap tokOpt) = encodeCNF φ := by
  unfold flatTokens encodeCNF
  induction φ with
  | nil => simp [tokToBits]
  | cons c φ ih =>
    simp only [List.flatMap_cons]
    rw [List.flatMap_append, tokToBits_append, tokToBits_tokOpt_clause, ih]

private theorem flatTokens_map (f : ℕ → ℕ) (ψ : CNF) :
    flatTokens (ψ.map fun c => c.map fun l => (f l.1, l.2)) =
      (flatTokens ψ).map (Option.map fun l => (f l.1, l.2)) := by
  unfold flatTokens
  induction ψ with
  | nil => simp
  | cons c ψ ih =>
    simp only [List.map_cons, List.flatMap_cons, List.map_append, List.map_map, ih]
    rfl

private theorem flatTokens_reindexCNF (φ : CNF) :
    flatTokens (reindexCNF φ) =
      (flatTokens φ).map (Option.map fun l => (reindexVar φ l.1, l.2)) :=
  flatTokens_map (reindexVar φ) φ

private theorem length_tokToBits (ts : List (Bool × Bool)) :
    (tokToBits ts).length = 2 * ts.length := by
  induction ts with
  | nil => simp [tokToBits]
  | cons p ts ih =>
    simp only [tokToBits, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

private theorem length_tokOpt_pos (o : Option Literal) : 1 ≤ (tokOpt o).length := by
  cases o with
  | none => simp [tokOpt]
  | some l => simp [tokOpt, tokLit]

private theorem length_le_flatMap_tokOpt (ts : List (Option Literal)) :
    ts.length ≤ (ts.flatMap tokOpt).length := by
  induction ts with
  | nil => simp
  | cons o ts ih =>
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    have := length_tokOpt_pos o
    omega

private theorem mem_bits_length_le {ts : List (Option Literal)} {l : Literal} (h : some l ∈ ts) :
    l.1.bits.length + 2 ≤ (ts.flatMap tokOpt).length := by
  induction ts with
  | nil => cases h
  | cons o ts ih =>
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp h with rfl | hmem
    · simp only [tokOpt, tokLit, List.length_cons, List.length_append, List.length_map,
        List.length_nil]
      omega
    · have := ih hmem
      omega

private theorem findIdx_le_length_tokOpt {ts : List (Option Literal)} {l : Literal}
    (h : some l ∈ ts) :
    ts.findIdx (fun o => o.any (fun l' => l'.1 == l.1)) ≤ (ts.flatMap tokOpt).length := by
  have h1 : ts.findIdx (fun o => o.any (fun l' => l'.1 == l.1)) < ts.length :=
    List.findIdx_lt_length_of_exists ⟨some l, h, by simp⟩
  have h2 := length_le_flatMap_tokOpt ts
  omega

private theorem reindexed_length_le (F : List (Option Literal)) (L : ℕ)
    (hF : (F.flatMap tokOpt).length = L) (f : ℕ → ℕ)
    (hf : ∀ l, some l ∈ F → f l.1 ≤ L) :
    ((F.map (Option.map fun l => (f l.1, l.2))).flatMap tokOpt).length ≤ L * (L + 2) := by
  have haux : ∀ ts : List (Option Literal), (∀ l, some l ∈ ts → f l.1 ≤ L) →
      ((ts.map (Option.map fun l => (f l.1, l.2))).flatMap tokOpt).length ≤ ts.length * (L + 2) := by
    intro ts
    induction ts with
    | nil => intro _; simp
    | cons o ts ih =>
      intro hts
      simp only [List.map_cons, List.flatMap_cons, List.length_append, List.length_cons]
      have htail := ih (fun l hl => hts l (List.mem_cons_of_mem o hl))
      cases o with
      | none =>
        simp only [Option.map_none, tokOpt, List.length_cons, List.length_nil]
        nlinarith
      | some l =>
        have hfl := hts l (List.mem_cons_self)
        have hbl := bits_length_le (f l.1)
        simp only [Option.map_some, tokOpt, tokLit, List.length_cons, List.length_append,
          List.length_map, List.length_nil]
        nlinarith
  have h1 := haux F hf
  have h2 : F.length ≤ L := by rw [← hF]; exact length_le_flatMap_tokOpt F
  nlinarith

private abbrev StΓ : Fin 10 → Type
  | ⟨0, _⟩ => Bool
  | ⟨1, _⟩ => Bool
  | ⟨2, _⟩ => Bool
  | ⟨3, _⟩ => Bool
  | ⟨4, _⟩ => Bool
  | ⟨5, _⟩ => Bool
  | ⟨6, _⟩ => Bool × Bool
  | ⟨7, _⟩ => Bool × Bool
  | ⟨8, _⟩ => Bool × Bool
  | ⟨9, _⟩ => Bool × Bool

private abbrev kInp : Fin 10 := ⟨0, by decide⟩
private abbrev kOut : Fin 10 := ⟨1, by decide⟩
private abbrev kCurVar : Fin 10 := ⟨2, by decide⟩
private abbrev kCurVarRev : Fin 10 := ⟨3, by decide⟩
private abbrev kCnt : Fin 10 := ⟨4, by decide⟩
private abbrev kCntTmp : Fin 10 := ⟨5, by decide⟩
private abbrev kOrig : Fin 10 := ⟨6, by decide⟩
private abbrev kOrigRev : Fin 10 := ⟨7, by decide⟩
private abbrev kRem : Fin 10 := ⟨8, by decide⟩
private abbrev kOutRev : Fin 10 := ⟨9, by decide⟩

private abbrev StS : Type := Option (Bool × Bool) × Option Bool
private def initS : StS := (none, none)

private abbrev lParse : Fin 16 := ⟨0, by decide⟩
private abbrev lDup : Fin 16 := ⟨1, by decide⟩
private abbrev lMain : Fin 16 := ⟨2, by decide⟩
private abbrev lReadVar : Fin 16 := ⟨3, by decide⟩
private abbrev lRevVar : Fin 16 := ⟨4, by decide⟩
private abbrev lSearch : Fin 16 := ⟨5, by decide⟩
private abbrev lCmp : Fin 16 := ⟨6, by decide⟩
private abbrev lSkipLit : Fin 16 := ⟨7, by decide⟩
private abbrev lRestoreVar : Fin 16 := ⟨8, by decide⟩
private abbrev lIncCarry : Fin 16 := ⟨9, by decide⟩
private abbrev lIncRestore : Fin 16 := ⟨10, by decide⟩
private abbrev lEmitIdx : Fin 16 := ⟨11, by decide⟩
private abbrev lClearVar : Fin 16 := ⟨12, by decide⟩
private abbrev lRewindOrig : Fin 16 := ⟨13, by decide⟩
private abbrev lClearOrig : Fin 16 := ⟨14, by decide⟩
private abbrev lEmitOut : Fin 16 := ⟨15, by decide⟩

private def go (l : Fin 16) : TM2.Stmt StΓ (Fin 16) StS :=
  .load (fun _ => initS) (.goto fun _ => l)

private def prog : Fin 16 → TM2.Stmt StΓ (Fin 16) StS
  | ⟨0, _⟩ =>
    .pop kInp (fun _ o => (o.map fun a => (a, false), none))
      (.branch (fun s => s.1.isSome)
        (.pop kInp (fun s o => (s.1, o))
          (.push kOrigRev (fun s => ((s.1.getD (false, false)).1, s.2.getD false))
            (go lParse)))
        (go lDup))
  | ⟨1, _⟩ =>
    .pop kOrigRev (fun _ o => (o, none))
      (.branch (fun s => s.1.isSome)
        (.push kOrig (fun s => s.1.getD (false, false))
          (.push kRem (fun s => s.1.getD (false, false))
            (go lDup)))
        (go lMain))
  | ⟨2, _⟩ =>
    .pop kRem (fun _ o => (o, none))
      (.branch (fun s => s.1.isSome)
        (.push kOutRev (fun s => s.1.getD (false, false))
          (.branch (fun s => (s.1.getD (false, false)).1)
            (go lReadVar)
            (go lMain)))
        (go lClearOrig))
  | ⟨3, _⟩ =>
    .pop kRem (fun _ o => (o, none))
      (.branch (fun s => (s.1.getD (false, false)).1)
        (.push kCurVarRev (fun s => (s.1.getD (false, false)).2)
          (go lReadVar))
        (go lRevVar))
  | ⟨4, _⟩ =>
    .pop kCurVarRev (fun _ o => (none, o))
      (.branch (fun s => s.2.isSome)
        (.push kCurVar (fun s => s.2.getD false)
          (go lRevVar))
        (go lSearch))
  | ⟨5, _⟩ =>
    .pop kOrig (fun _ o => (o, none))
      (.push kOrigRev (fun s => s.1.getD (false, false))
        (.branch (fun s => (s.1.getD (false, false)).1)
          (go lCmp)
          (go lIncCarry)))
  | ⟨6, _⟩ =>
    .pop kOrig (fun _ o => (o, none))
      (.push kOrigRev (fun s => s.1.getD (false, false))
        (.pop kCurVar (fun s o => (s.1, o))
          (.branch (fun s => (s.1.getD (false, false)).1)
            (.branch (fun s => s.2.isSome)
              (.push kCurVarRev (fun s => s.2.getD false)
                (.branch (fun s => (s.1.getD (false, false)).2 == s.2.getD false)
                  (go lCmp)
                  (go lSkipLit)))
              (go lSkipLit))
            (.branch (fun s => s.2.isSome)
              (.push kCurVarRev (fun s => s.2.getD false)
                (go lRestoreVar))
              (go lEmitIdx)))))
  | ⟨7, _⟩ =>
    .pop kOrig (fun _ o => (o, none))
      (.push kOrigRev (fun s => s.1.getD (false, false))
        (.branch (fun s => (s.1.getD (false, false)).1)
          (go lSkipLit)
          (go lRestoreVar)))
  | ⟨8, _⟩ =>
    .pop kCurVarRev (fun _ o => (none, o))
      (.branch (fun s => s.2.isSome)
        (.push kCurVar (fun s => s.2.getD false)
          (go lRestoreVar))
        (go lIncCarry))
  | ⟨9, _⟩ =>
    .pop kCnt (fun _ o => (none, o))
      (.branch (fun s => s.2 == some true)
        (.push kCntTmp (fun _ => false)
          (go lIncCarry))
        (.push kCnt (fun _ => true)
          (go lIncRestore)))
  | ⟨10, _⟩ =>
    .pop kCntTmp (fun _ o => (none, o))
      (.branch (fun s => s.2.isSome)
        (.push kCnt (fun s => s.2.getD false)
          (go lIncRestore))
        (go lSearch))
  | ⟨11, _⟩ =>
    .pop kCnt (fun _ o => (none, o))
      (.branch (fun s => s.2.isSome)
        (.push kOutRev (fun s => (true, s.2.getD false))
          (go lEmitIdx))
        (.push kOutRev (fun _ => (false, true))
          (go lClearVar)))
  | ⟨12, _⟩ =>
    .pop kCurVarRev (fun _ o => (none, o))
      (.branch (fun s => s.2.isSome)
        (go lClearVar)
        (go lRewindOrig))
  | ⟨13, _⟩ =>
    .pop kOrigRev (fun _ o => (o, none))
      (.branch (fun s => s.1.isSome)
        (.push kOrig (fun s => s.1.getD (false, false))
          (go lRewindOrig))
        (go lMain))
  | ⟨14, _⟩ =>
    .pop kOrig (fun _ o => (o, none))
      (.branch (fun s => s.1.isSome)
        (go lClearOrig)
        (go lEmitOut))
  | ⟨15, _⟩ =>
    .pop kOutRev (fun _ o => (o, none))
      (.branch (fun s => s.1.isSome)
        (.push kOut (fun s => (s.1.getD (false, false)).2)
          (.push kOut (fun s => (s.1.getD (false, false)).1)
            (go lEmitOut)))
        (.load (fun _ => initS) .halt))
  | ⟨_ + 16, h⟩ => absurd h (by omega)

private abbrev tm : FinTM2 where
  K := Fin 10
  k₀ := kInp
  k₁ := kOut
  Γ := StΓ
  Λ := Fin 16
  main := lParse
  σ := StS
  initialState := initS
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := prog

private abbrev MCfg : Type := TM2.Cfg StΓ (Fin 16) StS

private def mkStk
    (inp out curVar curVarRev cnt cntTmp : List Bool)
    (orig origRev rem outRev : List (Bool × Bool)) :
    ∀ k : Fin 10, List (StΓ k)
  | ⟨0, _⟩ => inp
  | ⟨1, _⟩ => out
  | ⟨2, _⟩ => curVar
  | ⟨3, _⟩ => curVarRev
  | ⟨4, _⟩ => cnt
  | ⟨5, _⟩ => cntTmp
  | ⟨6, _⟩ => orig
  | ⟨7, _⟩ => origRev
  | ⟨8, _⟩ => rem
  | ⟨9, _⟩ => outRev

private def cfg (l : Option (Fin 16))
    (inp out curVar curVarRev cnt cntTmp : List Bool)
    (orig origRev rem outRev : List (Bool × Bool)) : MCfg :=
  ⟨l, initS, mkStk inp out curVar curVarRev cnt cntTmp orig origRev rem outRev⟩

private theorem upd_inp (inp inp' out curVar curVarRev cnt cntTmp orig origRev rem outRev) :
    Function.update (mkStk inp out curVar curVarRev cnt cntTmp orig origRev rem outRev) kInp inp' =
      mkStk inp' out curVar curVarRev cnt cntTmp orig origRev rem outRev := by
  funext k; fin_cases k <;> rfl

private theorem upd_out (inp out out' curVar curVarRev cnt cntTmp orig origRev rem outRev) :
    Function.update (mkStk inp out curVar curVarRev cnt cntTmp orig origRev rem outRev) kOut out' =
      mkStk inp out' curVar curVarRev cnt cntTmp orig origRev rem outRev := by
  funext k; fin_cases k <;> rfl

private theorem upd_curVar (inp out curVar curVar' curVarRev cnt cntTmp orig origRev rem outRev) :
    Function.update (mkStk inp out curVar curVarRev cnt cntTmp orig origRev rem outRev) kCurVar curVar' =
      mkStk inp out curVar' curVarRev cnt cntTmp orig origRev rem outRev := by
  funext k; fin_cases k <;> rfl

private theorem upd_curVarRev (inp out curVar curVarRev curVarRev' cnt cntTmp orig origRev rem outRev) :
    Function.update (mkStk inp out curVar curVarRev cnt cntTmp orig origRev rem outRev) kCurVarRev curVarRev' =
      mkStk inp out curVar curVarRev' cnt cntTmp orig origRev rem outRev := by
  funext k; fin_cases k <;> rfl

private theorem upd_cnt (inp out curVar curVarRev cnt cnt' cntTmp orig origRev rem outRev) :
    Function.update (mkStk inp out curVar curVarRev cnt cntTmp orig origRev rem outRev) kCnt cnt' =
      mkStk inp out curVar curVarRev cnt' cntTmp orig origRev rem outRev := by
  funext k; fin_cases k <;> rfl

private theorem upd_cntTmp (inp out curVar curVarRev cnt cntTmp cntTmp' orig origRev rem outRev) :
    Function.update (mkStk inp out curVar curVarRev cnt cntTmp orig origRev rem outRev) kCntTmp cntTmp' =
      mkStk inp out curVar curVarRev cnt cntTmp' orig origRev rem outRev := by
  funext k; fin_cases k <;> rfl

private theorem upd_orig (inp out curVar curVarRev cnt cntTmp orig orig' origRev rem outRev) :
    Function.update (mkStk inp out curVar curVarRev cnt cntTmp orig origRev rem outRev) kOrig orig' =
      mkStk inp out curVar curVarRev cnt cntTmp orig' origRev rem outRev := by
  funext k; fin_cases k <;> rfl

private theorem upd_origRev (inp out curVar curVarRev cnt cntTmp orig origRev origRev' rem outRev) :
    Function.update (mkStk inp out curVar curVarRev cnt cntTmp orig origRev rem outRev) kOrigRev origRev' =
      mkStk inp out curVar curVarRev cnt cntTmp orig origRev' rem outRev := by
  funext k; fin_cases k <;> rfl

private theorem upd_rem (inp out curVar curVarRev cnt cntTmp orig origRev rem rem' outRev) :
    Function.update (mkStk inp out curVar curVarRev cnt cntTmp orig origRev rem outRev) kRem rem' =
      mkStk inp out curVar curVarRev cnt cntTmp orig origRev rem' outRev := by
  funext k; fin_cases k <;> rfl

private theorem upd_outRev (inp out curVar curVarRev cnt cntTmp orig origRev rem outRev outRev') :
    Function.update (mkStk inp out curVar curVarRev cnt cntTmp orig origRev rem outRev) kOutRev outRev' =
      mkStk inp out curVar curVarRev cnt cntTmp orig origRev rem outRev' := by
  funext k; fin_cases k <;> rfl

private theorem init_cfg (s : List Bool) :
    initList tm s = cfg (some lParse) s [] [] [] [] [] [] [] [] [] := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

private theorem halt_cfg (s : List Bool) :
    haltList tm s = cfg none [] s [] [] [] [] [] [] [] [] := by
  unfold haltList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

private def Steps (c₁ c₂ : MCfg) (n : ℕ) : Prop :=
  (flip bind (TM2.step prog))^[n] (some c₁) = some c₂

private def ReachesIn (c₁ c₂ : MCfg) (B : ℕ) : Prop :=
  ∃ n ≤ B, Steps c₁ c₂ n

private theorem Steps.one {c₁ c₂ : MCfg} (h : TM2.step prog c₁ = some c₂) : Steps c₁ c₂ 1 := h

private theorem Steps.cons {c₁ c₂ c₃ : MCfg} {n : ℕ}
    (h₁ : TM2.step prog c₁ = some c₂) (h₂ : Steps c₂ c₃ n) : Steps c₁ c₃ (n + 1) := by
  unfold Steps at *
  rw [Function.iterate_succ_apply]
  have e : flip bind (TM2.step prog) (some c₁) = some c₂ := h₁
  rw [e]
  exact h₂

private theorem ReachesIn.of_steps {c₁ c₂ : MCfg} {n B : ℕ} (h : Steps c₁ c₂ n) (hb : n ≤ B) :
    ReachesIn c₁ c₂ B := ⟨n, hb, h⟩

private theorem ReachesIn.weaken {c₁ c₂ : MCfg} {B₁ B₂ : ℕ}
    (h : ReachesIn c₁ c₂ B₁) (hb : B₁ ≤ B₂) : ReachesIn c₁ c₂ B₂ := by
  obtain ⟨n, hn, hs⟩ := h
  exact ⟨n, hn.trans hb, hs⟩

private theorem ReachesIn.trans {c₁ c₂ c₃ : MCfg} {B₁ B₂ : ℕ}
    (h₁ : ReachesIn c₁ c₂ B₁) (h₂ : ReachesIn c₂ c₃ B₂) : ReachesIn c₁ c₃ (B₁ + B₂) := by
  obtain ⟨n₁, hn₁, hs₁⟩ := h₁
  obtain ⟨n₂, hn₂, hs₂⟩ := h₂
  refine ⟨n₁ + n₂, Nat.add_le_add hn₁ hn₂, ?_⟩
  unfold Steps at *
  rw [Nat.add_comm, Function.iterate_add_apply, hs₁, hs₂]

private theorem ReachesIn.step {c₁ c₂ c₃ : MCfg} {B : ℕ}
    (h₁ : TM2.step prog c₁ = some c₂) (h₂ : ReachesIn c₂ c₃ B) : ReachesIn c₁ c₃ (B + 1) := by
  obtain ⟨n, hn, hs⟩ := h₂
  exact ⟨n + 1, Nat.add_le_add_right hn 1, Steps.cons h₁ hs⟩

private theorem step_parse_cons (a b : Bool) (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lParse) (a :: b :: inp) out cv cvr cnt ct orig origRev rem outRev) =
      some (cfg (some lParse) inp out cv cvr cnt ct orig ((a, b) :: origRev) rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_inp, upd_origRev,
    List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some,
    Option.getD_some, Bool.cond_true]

private theorem step_parse_nil (out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lParse) [] out cv cvr cnt ct orig origRev rem outRev) =
      some (cfg (some lDup) [] out cv cvr cnt ct orig origRev rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_inp,
    List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, Bool.cond_false]

private theorem run_parse (ts : List (Bool × Bool)) (origRev : List (Bool × Bool)) :
    Steps (cfg (some lParse) (tokToBits ts) [] [] [] [] [] [] origRev [] [])
      (cfg (some lDup) [] [] [] [] [] [] [] (ts.reverse ++ origRev) [] [])
      (ts.length + 1) := by
  induction ts generalizing origRev with
  | nil =>
    exact Steps.one (step_parse_nil [] [] [] [] [] [] origRev [] [])
  | cons p ts ih =>
    rcases p with ⟨a, b⟩
    rw [tokToBits_cons, List.length_cons]
    refine Steps.cons (step_parse_cons a b _ [] [] [] [] [] [] origRev [] []) ?_
    simpa [List.reverse_cons, List.append_assoc] using ih ((a, b) :: origRev)

private theorem step_dup_cons (p : Bool × Bool) (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lDup) inp out cv cvr cnt ct orig (p :: origRev) rem outRev) =
      some (cfg (some lDup) inp out cv cvr cnt ct (p :: orig) origRev (p :: rem) outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_origRev, upd_orig, upd_rem,
    List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some, Bool.cond_true]

private theorem step_dup_nil (inp out cv cvr cnt ct orig rem outRev) :
    TM2.step prog (cfg (some lDup) inp out cv cvr cnt ct orig [] rem outRev) =
      some (cfg (some lMain) inp out cv cvr cnt ct orig [] rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_origRev,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]

private theorem run_dup (origRev orig rem : List (Bool × Bool)) :
    Steps (cfg (some lDup) [] [] [] [] [] [] orig origRev rem [])
      (cfg (some lMain) [] [] [] [] [] [] (origRev.reverse ++ orig) [] (origRev.reverse ++ rem) [])
      (origRev.length + 1) := by
  induction origRev generalizing orig rem with
  | nil => exact Steps.one (step_dup_nil [] [] [] [] [] [] orig rem [])
  | cons p r ih =>
    simp only [List.length_cons]
    refine Steps.cons (step_dup_cons p [] [] [] [] [] [] orig r rem []) ?_
    simpa [List.reverse_cons, List.append_assoc] using ih (p :: orig) (p :: rem)

private theorem step_main_nil (inp out cv cvr cnt ct orig origRev outRev) :
    TM2.step prog (cfg (some lMain) inp out cv cvr cnt ct orig origRev [] outRev) =
      some (cfg (some lClearOrig) inp out cv cvr cnt ct orig origRev [] outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_rem,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]

private theorem step_main_false (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lMain) inp out cv cvr cnt ct orig origRev ((false, false) :: rem) outRev) =
      some (cfg (some lMain) inp out cv cvr cnt ct orig origRev rem ((false, false) :: outRev)) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_rem, upd_outRev,
    List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    Bool.cond_true, Bool.cond_false]

private theorem step_main_true (pol : Bool) (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lMain) inp out cv cvr cnt ct orig origRev ((true, pol) :: rem) outRev) =
      some (cfg (some lReadVar) inp out cv cvr cnt ct orig origRev rem ((true, pol) :: outRev)) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_rem, upd_outRev,
    List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some, Bool.cond_true]

private theorem step_readVar_true (d : Bool) (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lReadVar) inp out cv cvr cnt ct orig origRev ((true, d) :: rem) outRev) =
      some (cfg (some lReadVar) inp out cv (d :: cvr) cnt ct orig origRev rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_rem, upd_curVarRev,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_true]

private theorem step_readVar_end (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lReadVar) inp out cv cvr cnt ct orig origRev ((false, true) :: rem) outRev) =
      some (cfg (some lRevVar) inp out cv cvr cnt ct orig origRev rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_rem,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_false]

private theorem run_readVar (bs : List Bool) (cvr : List Bool) (orig rem outRev : List (Bool × Bool)) :
    Steps (cfg (some lReadVar) [] [] [] cvr [] [] orig [] ((bs.map fun d => (true, d)) ++ (false, true) :: rem) outRev)
      (cfg (some lRevVar) [] [] [] (bs.reverse ++ cvr) [] [] orig [] rem outRev)
      (bs.length + 1) := by
  induction bs generalizing cvr with
  | nil => exact Steps.one (step_readVar_end [] [] [] cvr [] [] orig [] rem outRev)
  | cons d bs ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    refine Steps.cons (step_readVar_true d [] [] [] cvr [] [] orig [] _ outRev) ?_
    simpa [List.reverse_cons, List.append_assoc] using ih (d :: cvr)

private theorem step_revVar_cons (d : Bool) (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lRevVar) inp out cv (d :: cvr) cnt ct orig origRev rem outRev) =
      some (cfg (some lRevVar) inp out (d :: cv) cvr cnt ct orig origRev rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_curVarRev, upd_curVar,
    List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some, Bool.cond_true]

private theorem step_revVar_nil (inp out cv cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lRevVar) inp out cv [] cnt ct orig origRev rem outRev) =
      some (cfg (some lSearch) inp out cv [] cnt ct orig origRev rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_curVarRev,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]

private theorem run_revVar (cvr cv : List Bool) (orig rem outRev : List (Bool × Bool)) :
    Steps (cfg (some lRevVar) [] [] cv cvr [] [] orig [] rem outRev)
      (cfg (some lSearch) [] [] (cvr.reverse ++ cv) [] [] [] orig [] rem outRev)
      (cvr.length + 1) := by
  induction cvr generalizing cv with
  | nil => exact Steps.one (step_revVar_nil [] [] cv [] [] orig [] rem outRev)
  | cons d cvr ih =>
    simp only [List.length_cons]
    refine Steps.cons (step_revVar_cons d [] [] cv cvr [] [] orig [] rem outRev) ?_
    simpa [List.reverse_cons, List.append_assoc] using ih (d :: cv)

private theorem step_search_false (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lSearch) inp out cv cvr cnt ct ((false, false) :: orig) origRev rem outRev) =
      some (cfg (some lIncCarry) inp out cv cvr cnt ct orig ((false, false) :: origRev) rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_orig, upd_origRev,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_false]

private theorem step_search_true (pol : Bool) (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lSearch) inp out cv cvr cnt ct ((true, pol) :: orig) origRev rem outRev) =
      some (cfg (some lCmp) inp out cv cvr cnt ct orig ((true, pol) :: origRev) rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_orig, upd_origRev,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_true]

private theorem step_cmp_tt_eq (d : Bool) (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lCmp) inp out (d :: cv) cvr cnt ct ((true, d) :: orig) origRev rem outRev) =
      some (cfg (some lCmp) inp out cv (d :: cvr) cnt ct orig ((true, d) :: origRev) rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_orig, upd_origRev, upd_curVar,
    upd_curVarRev, List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    beq_self_eq_true, Bool.cond_true]

private theorem step_cmp_tt_ne (d' d : Bool) (hne : d' ≠ d)
    (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lCmp) inp out (d :: cv) cvr cnt ct ((true, d') :: orig) origRev rem outRev) =
      some (cfg (some lSkipLit) inp out cv (d :: cvr) cnt ct orig ((true, d') :: origRev) rem outRev) := by
  have hb : (d' == d) = false := beq_false_of_ne hne
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_orig, upd_origRev, upd_curVar,
    upd_curVarRev, List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    hb, Bool.cond_true, Bool.cond_false]

private theorem step_cmp_t_nil (d' : Bool) (inp out cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lCmp) inp out [] cvr cnt ct ((true, d') :: orig) origRev rem outRev) =
      some (cfg (some lSkipLit) inp out [] cvr cnt ct orig ((true, d') :: origRev) rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_orig, upd_origRev, upd_curVar,
    List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil, Option.isSome_none,
    Option.getD_some, Bool.cond_true, Bool.cond_false]

private theorem step_cmp_f_cons (d : Bool) (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lCmp) inp out (d :: cv) cvr cnt ct ((false, true) :: orig) origRev rem outRev) =
      some (cfg (some lRestoreVar) inp out cv (d :: cvr) cnt ct orig ((false, true) :: origRev) rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_orig, upd_origRev, upd_curVar,
    upd_curVarRev, List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    Bool.cond_true, Bool.cond_false]

private theorem step_cmp_f_nil (inp out cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lCmp) inp out [] cvr cnt ct ((false, true) :: orig) origRev rem outRev) =
      some (cfg (some lEmitIdx) inp out [] cvr cnt ct orig ((false, true) :: origRev) rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_orig, upd_origRev, upd_curVar,
    List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil, Option.isSome_none,
    Option.getD_some, Bool.cond_false]

private theorem step_skipLit_true (d : Bool) (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lSkipLit) inp out cv cvr cnt ct ((true, d) :: orig) origRev rem outRev) =
      some (cfg (some lSkipLit) inp out cv cvr cnt ct orig ((true, d) :: origRev) rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_orig, upd_origRev,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_true]

private theorem step_skipLit_end (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lSkipLit) inp out cv cvr cnt ct ((false, true) :: orig) origRev rem outRev) =
      some (cfg (some lRestoreVar) inp out cv cvr cnt ct orig ((false, true) :: origRev) rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_orig, upd_origRev,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_false]

private theorem run_skipLit (bs : List Bool) (cv cvr cnt : List Bool)
    (orig origRev rem outRev : List (Bool × Bool)) :
    Steps (cfg (some lSkipLit) [] [] cv cvr cnt [] ((bs.map fun d => (true, d)) ++ (false, true) :: orig) origRev rem outRev)
      (cfg (some lRestoreVar) [] [] cv cvr cnt [] orig ((false, true) :: (bs.map fun d => (true, d)).reverse ++ origRev) rem outRev)
      (bs.length + 1) := by
  induction bs generalizing origRev with
  | nil => exact Steps.one (step_skipLit_end [] [] cv cvr cnt [] orig origRev rem outRev)
  | cons d bs ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    refine Steps.cons (step_skipLit_true d [] [] cv cvr cnt [] _ origRev rem outRev) ?_
    simpa [List.reverse_cons, List.append_assoc] using ih ((true, d) :: origRev)

private theorem step_restoreVar_cons (d : Bool) (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lRestoreVar) inp out cv (d :: cvr) cnt ct orig origRev rem outRev) =
      some (cfg (some lRestoreVar) inp out (d :: cv) cvr cnt ct orig origRev rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_curVarRev, upd_curVar,
    List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some, Bool.cond_true]

private theorem step_restoreVar_nil (inp out cv cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lRestoreVar) inp out cv [] cnt ct orig origRev rem outRev) =
      some (cfg (some lIncCarry) inp out cv [] cnt ct orig origRev rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_curVarRev,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]

private theorem run_restoreVar (cvr cv cnt : List Bool) (orig origRev rem outRev : List (Bool × Bool)) :
    Steps (cfg (some lRestoreVar) [] [] cv cvr cnt [] orig origRev rem outRev)
      (cfg (some lIncCarry) [] [] (cvr.reverse ++ cv) [] cnt [] orig origRev rem outRev)
      (cvr.length + 1) := by
  induction cvr generalizing cv with
  | nil => exact Steps.one (step_restoreVar_nil [] [] cv cnt [] orig origRev rem outRev)
  | cons d cvr ih =>
    simp only [List.length_cons]
    refine Steps.cons (step_restoreVar_cons d [] [] cv cvr cnt [] orig origRev rem outRev) ?_
    simpa [List.reverse_cons, List.append_assoc] using ih (d :: cv)

private theorem step_incCarry_true (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lIncCarry) inp out cv cvr (true :: cnt) ct orig origRev rem outRev) =
      some (cfg (some lIncCarry) inp out cv cvr cnt (false :: ct) orig origRev rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_cnt, upd_cntTmp,
    List.head?_cons, List.tail_cons, beq_self_eq_true, Bool.cond_true]

private theorem step_incCarry_false (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lIncCarry) inp out cv cvr (false :: cnt) ct orig origRev rem outRev) =
      some (cfg (some lIncRestore) inp out cv cvr (true :: cnt) ct orig origRev rem outRev) := by
  have hb : (some false == some true) = false := rfl
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_cnt,
    List.head?_cons, List.tail_cons, hb, Bool.cond_false]

private theorem step_incCarry_nil (inp out cv cvr ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lIncCarry) inp out cv cvr [] ct orig origRev rem outRev) =
      some (cfg (some lIncRestore) inp out cv cvr [true] ct orig origRev rem outRev) := by
  have hb : ((none : Option Bool) == some true) = false := rfl
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_cnt,
    List.head?_nil, List.tail_nil, hb, Bool.cond_false]

private theorem step_incRestore_cons (b : Bool) (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lIncRestore) inp out cv cvr cnt (b :: ct) orig origRev rem outRev) =
      some (cfg (some lIncRestore) inp out cv cvr (b :: cnt) ct orig origRev rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_cntTmp, upd_cnt,
    List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some, Bool.cond_true]

private theorem step_incRestore_nil (inp out cv cvr cnt orig origRev rem outRev) :
    TM2.step prog (cfg (some lIncRestore) inp out cv cvr cnt [] orig origRev rem outRev) =
      some (cfg (some lSearch) inp out cv cvr cnt [] orig origRev rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_cntTmp,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]

private theorem run_incRestore (ct cnt cv : List Bool) (orig origRev rem outRev : List (Bool × Bool)) :
    Steps (cfg (some lIncRestore) [] [] cv [] cnt ct orig origRev rem outRev)
      (cfg (some lSearch) [] [] cv [] (ct.reverse ++ cnt) [] orig origRev rem outRev)
      (ct.length + 1) := by
  induction ct generalizing cnt with
  | nil => exact Steps.one (step_incRestore_nil [] [] cv [] cnt orig origRev rem outRev)
  | cons b ct ih =>
    simp only [List.length_cons]
    refine Steps.cons (step_incRestore_cons b [] [] cv [] cnt ct orig origRev rem outRev) ?_
    simpa [List.reverse_cons, List.append_assoc] using ih (b :: cnt)

private theorem run_inc (cnt ct cv : List Bool) (orig origRev rem outRev : List (Bool × Bool)) :
    ReachesIn (cfg (some lIncCarry) [] [] cv [] cnt ct orig origRev rem outRev)
      (cfg (some lSearch) [] [] cv [] (ct.reverse ++ incBits cnt) [] orig origRev rem outRev)
      (2 * cnt.length + ct.length + 2) := by
  induction cnt generalizing ct with
  | nil =>
    have h1 := step_incCarry_nil [] [] cv [] ct orig origRev rem outRev
    have h2 := run_incRestore ct [true] cv orig origRev rem outRev
    refine ReachesIn.of_steps (Steps.cons h1 h2) ?_
    simp
  | cons b cnt ih =>
    cases b with
    | false =>
      have h1 := step_incCarry_false [] [] cv [] cnt ct orig origRev rem outRev
      have h2 := run_incRestore ct (true :: cnt) cv orig origRev rem outRev
      refine ReachesIn.of_steps (Steps.cons h1 h2) ?_
      simp
    | true =>
      have h1 := step_incCarry_true [] [] cv [] cnt ct orig origRev rem outRev
      have h2 := ih (false :: ct)
      have h3 := ReachesIn.step h1 h2
      have eqc : (false :: ct).reverse ++ incBits cnt = ct.reverse ++ incBits (true :: cnt) := by
        simp [incBits, List.reverse_cons, List.append_assoc]
      rw [eqc] at h3
      refine h3.weaken ?_
      simp
      omega

private theorem run_cmp_match (bs cvr cnt : List Bool) (orig origRev rem outRev : List (Bool × Bool)) :
    Steps (cfg (some lCmp) [] [] bs cvr cnt [] ((bs.map fun d => (true, d)) ++ (false, true) :: orig) origRev rem outRev)
      (cfg (some lEmitIdx) [] [] [] (bs.reverse ++ cvr) cnt [] orig ((false, true) :: (bs.map fun d => (true, d)).reverse ++ origRev) rem outRev)
      (bs.length + 1) := by
  induction bs generalizing cvr origRev with
  | nil =>
    exact Steps.one (step_cmp_f_nil [] [] cvr cnt [] orig origRev rem outRev)
  | cons d bs ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    refine Steps.cons (step_cmp_tt_eq d [] [] bs cvr cnt [] _ origRev rem outRev) ?_
    simpa [List.reverse_cons, List.append_assoc] using ih (d :: cvr) ((true, d) :: origRev)

private theorem run_cmp_mismatch (bs' bs cvr cnt : List Bool) (hne : bs' ≠ bs)
    (orig origRev rem outRev : List (Bool × Bool)) :
    ReachesIn (cfg (some lCmp) [] [] bs cvr cnt [] ((bs'.map fun d => (true, d)) ++ (false, true) :: orig) origRev rem outRev)
      (cfg (some lIncCarry) [] [] (cvr.reverse ++ bs) [] cnt [] orig ((false, true) :: (bs'.map fun d => (true, d)).reverse ++ origRev) rem outRev)
      (bs'.length + cvr.length + bs.length + 2) := by
  induction bs' generalizing bs cvr origRev with
  | nil =>
    cases bs with
    | nil => exact absurd rfl hne
    | cons d bs =>
      have h1 := step_cmp_f_cons d [] [] bs cvr cnt [] orig origRev rem outRev
      have h2 := run_restoreVar (d :: cvr) bs cnt orig ((false, true) :: origRev) rem outRev
      have h2' : Steps
          (cfg (some lRestoreVar) [] [] bs (d :: cvr) cnt [] orig ((false, true) :: origRev) rem outRev)
          (cfg (some lIncCarry) [] [] (cvr.reverse ++ d :: bs) [] cnt [] orig ((false, true) :: origRev) rem outRev)
          ((d :: cvr).length + 1) := by
        simpa [List.reverse_cons, List.append_assoc] using h2
      refine ReachesIn.of_steps (Steps.cons h1 h2') ?_
      simp
  | cons d' bs' ih =>
    cases bs with
    | nil =>
      have h1 := step_cmp_t_nil d' [] [] cvr cnt [] ((bs'.map fun d => (true, d)) ++ (false, true) :: orig) origRev rem outRev
      have h2 := run_skipLit bs' [] cvr cnt orig ((true, d') :: origRev) rem outRev
      have h3 := run_restoreVar cvr [] cnt orig ((false, true) :: (bs'.map fun d => (true, d)).reverse ++ (true, d') :: origRev) rem outRev
      have h23 : ReachesIn
          (cfg (some lSkipLit) [] [] [] cvr cnt [] ((bs'.map fun d => (true, d)) ++ (false, true) :: orig) ((true, d') :: origRev) rem outRev)
          (cfg (some lIncCarry) [] [] (cvr.reverse ++ []) [] cnt [] orig ((false, true) :: ((d' :: bs').map fun d => (true, d)).reverse ++ origRev) rem outRev)
          ((bs'.length + 1) + (cvr.length + 1)) := by
        refine (ReachesIn.of_steps h2 le_rfl).trans ?_
        simpa [List.map_cons, List.reverse_cons, List.append_assoc] using ReachesIn.of_steps h3 le_rfl
      refine (ReachesIn.step h1 h23).weaken ?_
      simp; omega
    | cons d bs =>
      by_cases hd : d' = d
      · subst hd
        have htl : bs' ≠ bs := fun h => hne (congrArg (List.cons d') h)
        have h1 := step_cmp_tt_eq d' [] [] bs cvr cnt [] ((bs'.map fun d => (true, d)) ++ (false, true) :: orig) origRev rem outRev
        have h2 := ih bs (d' :: cvr) htl ((true, d') :: origRev)
        have h3 := ReachesIn.step h1 h2
        have eq1 : (d' :: cvr).reverse ++ bs = cvr.reverse ++ d' :: bs := by
          simp [List.reverse_cons, List.append_assoc]
        have eq2 : (false, true) :: (bs'.map fun d => (true, d)).reverse ++ (true, d') :: origRev =
            (false, true) :: ((d' :: bs').map fun d => (true, d)).reverse ++ origRev := by
          simp [List.map_cons, List.reverse_cons, List.append_assoc]
        rw [eq1, eq2] at h3
        refine h3.weaken ?_
        simp; omega
      · have h1 := step_cmp_tt_ne d' d hd [] [] bs cvr cnt [] ((bs'.map fun d => (true, d)) ++ (false, true) :: orig) origRev rem outRev
        have h2 := run_skipLit bs' bs (d :: cvr) cnt orig ((true, d') :: origRev) rem outRev
        have h3 := run_restoreVar (d :: cvr) bs cnt orig ((false, true) :: (bs'.map fun d => (true, d)).reverse ++ (true, d') :: origRev) rem outRev
        have h23 : ReachesIn
            (cfg (some lSkipLit) [] [] bs (d :: cvr) cnt [] ((bs'.map fun d => (true, d)) ++ (false, true) :: orig) ((true, d') :: origRev) rem outRev)
            (cfg (some lIncCarry) [] [] (cvr.reverse ++ d :: bs) [] cnt [] orig ((false, true) :: ((d' :: bs').map fun d => (true, d)).reverse ++ origRev) rem outRev)
            ((bs'.length + 1) + ((d :: cvr).length + 1)) := by
          refine (ReachesIn.of_steps h2 le_rfl).trans ?_
          simpa [List.map_cons, List.reverse_cons, List.append_assoc] using ReachesIn.of_steps h3 le_rfl
        refine (ReachesIn.step h1 h23).weaken ?_
        simp; omega

private theorem run_search (L : ℕ) (v : ℕ) (hv : v.bits.length ≤ L)
    (ts : List (Option Literal)) (n : ℕ)
    (hfull : List (Bool × Bool))
    (origRev rem outRev : List (Bool × Bool))
    (hex : ∃ o ∈ ts, o.any (fun l' => l'.1 == v) = true)
    (hinv : origRev.reverse ++ ts.flatMap tokOpt = hfull)
    (hlen : hfull.length = L)
    (hn : n + ts.length ≤ L) :
    ∃ orig' origRev',
      origRev'.reverse ++ orig' = hfull ∧
      ReachesIn (cfg (some lSearch) [] [] v.bits [] n.bits [] (ts.flatMap tokOpt) origRev rem outRev)
        (cfg (some lEmitIdx) [] [] [] v.bits.reverse
          (n + ts.findIdx (fun o => o.any (fun l' => l'.1 == v))).bits [] orig' origRev' rem outRev)
        (ts.length * (4 * L + 5)) := by
  induction ts generalizing n origRev with
  | nil =>
    obtain ⟨o, ho, _⟩ := hex
    cases ho
  | cons o ts ih =>
    cases o with
    | none =>
      have hex' : ∃ o' ∈ ts, o'.any (fun l' => l'.1 == v) = true := by
        obtain ⟨o', ho', hp⟩ := hex
        rcases List.mem_cons.mp ho' with rfl | hm
        · simp at hp
        · exact ⟨o', hm, hp⟩
      have h1 := step_search_false [] [] v.bits [] n.bits [] (ts.flatMap tokOpt) origRev rem outRev
      have h2 := run_inc n.bits [] v.bits (ts.flatMap tokOpt) ((false, false) :: origRev) rem outRev
      simp only [List.reverse_nil, List.nil_append, incBits_bits, List.length_nil] at h2
      have hinv' : ((false, false) :: origRev).reverse ++ ts.flatMap tokOpt = hfull := by
        simpa [tokOpt, List.reverse_cons, List.append_assoc] using hinv
      have hn' : (n + 1) + ts.length ≤ L := by simp at hn; omega
      obtain ⟨orig', origRev', hinv2, hrest⟩ := ih (n + 1) ((false, false) :: origRev) hex' hinv' hn'
      refine ⟨orig', origRev', hinv2, ?_⟩
      have hstep := (ReachesIn.step h1 h2).trans hrest
      have hidx : (none :: ts).findIdx (fun o => o.any (fun l' => l'.1 == v)) =
          ts.findIdx (fun o => o.any (fun l' => l'.1 == v)) + 1 := by
        simp [List.findIdx_cons]
      have heq : n + 1 + ts.findIdx (fun o => o.any (fun l' => l'.1 == v)) =
          n + (none :: ts).findIdx (fun o => o.any (fun l' => l'.1 == v)) := by
        rw [hidx]; omega
      rw [heq] at hstep
      have hnb : n.bits.length ≤ L := (bits_length_le n).trans (by simp at hn; omega)
      refine hstep.weaken ?_
      simp only [List.length_cons]
      nlinarith
    | some l' =>
      by_cases hveq : l'.1 = v
      · have h1 := step_search_true l'.2 [] [] v.bits [] n.bits []
          ((l'.1.bits.map fun d => (true, d)) ++ (false, true) :: ts.flatMap tokOpt) origRev rem outRev
        have h2 := run_cmp_match v.bits [] n.bits (ts.flatMap tokOpt) ((true, l'.2) :: origRev) rem outRev
        simp only [List.append_nil] at h2
        rw [← hveq] at h2
        have hstep : ReachesIn
            (cfg (some lSearch) [] [] v.bits [] n.bits [] ((some l' :: ts).flatMap tokOpt) origRev rem outRev)
            (cfg (some lEmitIdx) [] [] [] v.bits.reverse n.bits []
              (ts.flatMap tokOpt)
              ((false, true) :: (l'.1.bits.map fun d => (true, d)).reverse ++ (true, l'.2) :: origRev)
              rem outRev)
            (v.bits.length + 2) := by
          have h12 : Steps
              (cfg (some lSearch) [] [] v.bits [] n.bits [] ((some l' :: ts).flatMap tokOpt) origRev rem outRev)
              (cfg (some lEmitIdx) [] [] [] v.bits.reverse n.bits []
                (ts.flatMap tokOpt)
                ((false, true) :: (l'.1.bits.map fun d => (true, d)).reverse ++ (true, l'.2) :: origRev)
                rem outRev)
              (l'.1.bits.length + 1 + 1) := by
            have h1' : TM2.step prog (cfg (some lSearch) [] [] v.bits [] n.bits []
                ((some l' :: ts).flatMap tokOpt) origRev rem outRev) =
                some (cfg (some lCmp) [] [] v.bits [] n.bits []
                  ((l'.1.bits.map fun d => (true, d)) ++ (false, true) :: ts.flatMap tokOpt)
                  ((true, l'.2) :: origRev) rem outRev) := by
              simpa [tokOpt, tokLit, List.flatMap_cons, List.cons_append, List.append_assoc] using h1
            have h2' : Steps
                (cfg (some lCmp) [] [] v.bits [] n.bits []
                  ((l'.1.bits.map fun d => (true, d)) ++ (false, true) :: ts.flatMap tokOpt)
                  ((true, l'.2) :: origRev) rem outRev)
                (cfg (some lEmitIdx) [] [] [] v.bits.reverse n.bits []
                  (ts.flatMap tokOpt)
                  ((false, true) :: (l'.1.bits.map fun d => (true, d)).reverse ++ (true, l'.2) :: origRev)
                  rem outRev)
                (l'.1.bits.length + 1) := by
              simpa [hveq] using h2
            exact Steps.cons h1' h2'
          refine ReachesIn.of_steps h12 ?_
          rw [hveq]
        have hidx : (some l' :: ts).findIdx (fun o => o.any (fun l'' => l''.1 == v)) = 0 := by
          simp [List.findIdx_cons, hveq]
        have hinv2 : ((false, true) :: (l'.1.bits.map fun d => (true, d)).reverse ++ (true, l'.2) :: origRev).reverse ++ ts.flatMap tokOpt = hfull := by
          rw [← hinv]
          simp [tokOpt, tokLit, List.flatMap_cons, List.reverse_cons, List.append_assoc]
        refine ⟨ts.flatMap tokOpt, (false, true) :: (l'.1.bits.map fun d => (true, d)).reverse ++ (true, l'.2) :: origRev, hinv2, ?_⟩
        rw [hidx, Nat.add_zero]
        refine hstep.weaken ?_
        simp only [List.length_cons]
        nlinarith
      · have hne_bits : l'.1.bits ≠ v.bits := fun h => hveq (bits_injective h)
        have hex' : ∃ o' ∈ ts, o'.any (fun l'' => l''.1 == v) = true := by
          obtain ⟨o', ho', hp⟩ := hex
          rcases List.mem_cons.mp ho' with rfl | hm
          · simp [hveq] at hp
          · exact ⟨o', hm, hp⟩
        have h1 : TM2.step prog (cfg (some lSearch) [] [] v.bits [] n.bits []
            ((some l' :: ts).flatMap tokOpt) origRev rem outRev) =
            some (cfg (some lCmp) [] [] v.bits [] n.bits []
              ((l'.1.bits.map fun d => (true, d)) ++ (false, true) :: ts.flatMap tokOpt)
              ((true, l'.2) :: origRev) rem outRev) := by
          simpa [tokOpt, tokLit, List.flatMap_cons, List.cons_append, List.append_assoc] using
            step_search_true l'.2 [] [] v.bits [] n.bits []
              ((l'.1.bits.map fun d => (true, d)) ++ (false, true) :: ts.flatMap tokOpt) origRev rem outRev
        have h2 := run_cmp_mismatch l'.1.bits v.bits [] n.bits hne_bits
          (ts.flatMap tokOpt) ((true, l'.2) :: origRev) rem outRev
        simp only [List.reverse_nil, List.nil_append, List.length_nil] at h2
        let origRev1 := (false, true) :: (l'.1.bits.map fun d => (true, d)).reverse ++ (true, l'.2) :: origRev
        have h3 := run_inc n.bits [] v.bits (ts.flatMap tokOpt) origRev1 rem outRev
        simp only [List.reverse_nil, List.nil_append, incBits_bits, List.length_nil] at h3
        have hinv' : origRev1.reverse ++ ts.flatMap tokOpt = hfull := by
          rw [← hinv]
          simp [origRev1, tokOpt, tokLit, List.flatMap_cons, List.reverse_cons, List.append_assoc]
        have hn' : (n + 1) + ts.length ≤ L := by simp at hn; omega
        obtain ⟨orig', origRev', hinv2, hrest⟩ := ih (n + 1) origRev1 hex' hinv' hn'
        refine ⟨orig', origRev', hinv2, ?_⟩
        have hstep := ((ReachesIn.step h1 h2).trans h3).trans hrest
        have hidx : (some l' :: ts).findIdx (fun o => o.any (fun l'' => l''.1 == v)) =
            ts.findIdx (fun o => o.any (fun l'' => l''.1 == v)) + 1 := by
          simp [List.findIdx_cons, hveq]
        have heq : n + 1 + ts.findIdx (fun o => o.any (fun l'' => l''.1 == v)) =
            n + (some l' :: ts).findIdx (fun o => o.any (fun l'' => l''.1 == v)) := by
          rw [hidx]; omega
        rw [heq] at hstep
        have hnb : n.bits.length ≤ L := (bits_length_le n).trans (by simp at hn; omega)
        have hl'b : l'.1.bits.length ≤ L := by
          have := mem_bits_length_le (ts := some l' :: ts) (l := l') List.mem_cons_self
          have hsub : ((some l' :: ts).flatMap tokOpt).length ≤ hfull.length := by
            rw [← hinv, List.length_append]
            omega
          omega
        refine hstep.weaken ?_
        simp only [List.length_cons]
        nlinarith

private theorem step_emitIdx_cons (b : Bool) (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lEmitIdx) inp out cv cvr (b :: cnt) ct orig origRev rem outRev) =
      some (cfg (some lEmitIdx) inp out cv cvr cnt ct orig origRev rem ((true, b) :: outRev)) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_cnt, upd_outRev,
    List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some, Bool.cond_true]

private theorem step_emitIdx_nil (inp out cv cvr ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lEmitIdx) inp out cv cvr [] ct orig origRev rem outRev) =
      some (cfg (some lClearVar) inp out cv cvr [] ct orig origRev rem ((false, true) :: outRev)) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_cnt, upd_outRev,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]

private theorem run_emitIdx (cnt cvr : List Bool) (orig origRev rem outRev : List (Bool × Bool)) :
    Steps (cfg (some lEmitIdx) [] [] [] cvr cnt [] orig origRev rem outRev)
      (cfg (some lClearVar) [] [] [] cvr [] [] orig origRev rem ((false, true) :: (cnt.map fun d => (true, d)).reverse ++ outRev))
      (cnt.length + 1) := by
  induction cnt generalizing outRev with
  | nil => exact Steps.one (step_emitIdx_nil [] [] [] cvr [] orig origRev rem outRev)
  | cons b cnt ih =>
    simp only [List.length_cons]
    refine Steps.cons (step_emitIdx_cons b [] [] [] cvr cnt [] orig origRev rem outRev) ?_
    simpa [List.map_cons, List.reverse_cons, List.append_assoc] using ih ((true, b) :: outRev)

private theorem step_clearVar_cons (b : Bool) (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lClearVar) inp out cv (b :: cvr) cnt ct orig origRev rem outRev) =
      some (cfg (some lClearVar) inp out cv cvr cnt ct orig origRev rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_curVarRev,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true]

private theorem step_clearVar_nil (inp out cv cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lClearVar) inp out cv [] cnt ct orig origRev rem outRev) =
      some (cfg (some lRewindOrig) inp out cv [] cnt ct orig origRev rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_curVarRev,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]

private theorem run_clearVar (cvr : List Bool) (orig origRev rem outRev : List (Bool × Bool)) :
    Steps (cfg (some lClearVar) [] [] [] cvr [] [] orig origRev rem outRev)
      (cfg (some lRewindOrig) [] [] [] [] [] [] orig origRev rem outRev)
      (cvr.length + 1) := by
  induction cvr with
  | nil => exact Steps.one (step_clearVar_nil [] [] [] [] [] orig origRev rem outRev)
  | cons b cvr ih =>
    simp only [List.length_cons]
    exact Steps.cons (step_clearVar_cons b [] [] [] cvr [] [] orig origRev rem outRev) ih

private theorem step_rewindOrig_cons (p : Bool × Bool) (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lRewindOrig) inp out cv cvr cnt ct orig (p :: origRev) rem outRev) =
      some (cfg (some lRewindOrig) inp out cv cvr cnt ct (p :: orig) origRev rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_origRev, upd_orig,
    List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some, Bool.cond_true]

private theorem step_rewindOrig_nil (inp out cv cvr cnt ct orig rem outRev) :
    TM2.step prog (cfg (some lRewindOrig) inp out cv cvr cnt ct orig [] rem outRev) =
      some (cfg (some lMain) inp out cv cvr cnt ct orig [] rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_origRev,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]

private theorem run_rewindOrig (origRev orig rem outRev : List (Bool × Bool)) :
    Steps (cfg (some lRewindOrig) [] [] [] [] [] [] orig origRev rem outRev)
      (cfg (some lMain) [] [] [] [] [] [] (origRev.reverse ++ orig) [] rem outRev)
      (origRev.length + 1) := by
  induction origRev generalizing orig with
  | nil => exact Steps.one (step_rewindOrig_nil [] [] [] [] [] [] orig rem outRev)
  | cons p r ih =>
    simp only [List.length_cons]
    refine Steps.cons (step_rewindOrig_cons p [] [] [] [] [] [] orig r rem outRev) ?_
    simpa [List.reverse_cons, List.append_assoc] using ih (p :: orig)

private theorem run_main (φ : CNF) (ts : List (Option Literal)) (outRev : List (Bool × Bool))
    (hmem : ∀ l, some l ∈ ts → some l ∈ flatTokens φ) :
    ReachesIn (cfg (some lMain) [] [] [] [] [] [] ((flatTokens φ).flatMap tokOpt) [] (ts.flatMap tokOpt) outRev)
      (cfg (some lClearOrig) [] [] [] [] [] [] ((flatTokens φ).flatMap tokOpt) [] []
        (((ts.map (Option.map fun l => (reindexVar φ l.1, l.2))).flatMap tokOpt).reverse ++ outRev))
      (ts.length * (4 * ((flatTokens φ).flatMap tokOpt).length ^ 2 +
        10 * ((flatTokens φ).flatMap tokOpt).length + 6) + 1) := by
  set F := flatTokens φ
  set hfull := F.flatMap tokOpt
  set L := hfull.length
  induction ts generalizing outRev with
  | nil =>
    have h1 := step_main_nil [] [] [] [] [] [] hfull [] outRev
    exact ReachesIn.of_steps (Steps.one h1) (by simp)
  | cons o ts ih =>
    cases o with
    | none =>
      have h1 := step_main_false [] [] [] [] [] [] hfull [] (ts.flatMap tokOpt) outRev
      have h2 := ih ((false, false) :: outRev) (fun l hl => hmem l (List.mem_cons_of_mem none hl))
      have h12 := ReachesIn.step h1 h2
      have eqout :
          (((ts.map (Option.map fun l => (reindexVar φ l.1, l.2))).flatMap tokOpt).reverse ++ (false, false) :: outRev) =
          ((((none :: ts).map (Option.map fun l => (reindexVar φ l.1, l.2))).flatMap tokOpt).reverse ++ outRev) := by
        simp [tokOpt, List.append_assoc]
      rw [eqout] at h12
      refine h12.weaken ?_
      simp only [List.length_cons]
      nlinarith
    | some l =>
      have hlF : some l ∈ F := hmem l List.mem_cons_self
      have hlb : l.1.bits.length ≤ L := by
        have := mem_bits_length_le hlF
        change l.1.bits.length ≤ (F.flatMap tokOpt).length
        omega
      have hFlen : F.length ≤ L := length_le_flatMap_tokOpt F
      have hidx_le : reindexVar φ l.1 ≤ L := findIdx_le_length_tokOpt hlF
      have hidxb : (reindexVar φ l.1).bits.length ≤ L := (bits_length_le _).trans hidx_le
      have h1 : TM2.step prog (cfg (some lMain) [] [] [] [] [] [] hfull []
          ((some l :: ts).flatMap tokOpt) outRev) =
          some (cfg (some lReadVar) [] [] [] [] [] [] hfull []
            ((l.1.bits.map fun d => (true, d)) ++ (false, true) :: ts.flatMap tokOpt)
            ((true, l.2) :: outRev)) := by
        simpa [tokOpt, tokLit, List.flatMap_cons, List.cons_append, List.append_assoc] using
          step_main_true l.2 [] [] [] [] [] [] hfull []
            ((l.1.bits.map fun d => (true, d)) ++ (false, true) :: ts.flatMap tokOpt) outRev
      have h2 := run_readVar l.1.bits [] hfull (ts.flatMap tokOpt) ((true, l.2) :: outRev)
      simp only [List.append_nil] at h2
      have h3 := run_revVar l.1.bits.reverse [] hfull (ts.flatMap tokOpt) ((true, l.2) :: outRev)
      simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h3
      have hex : ∃ o' ∈ F, o'.any (fun l' => l'.1 == l.1) = true := ⟨some l, hlF, by simp⟩
      obtain ⟨orig', origRev', hinv', h4⟩ := run_search L l.1 hlb F 0 hfull []
        (ts.flatMap tokOpt) ((true, l.2) :: outRev) hex (by simp [hfull]) rfl (by omega)
      simp only [Nat.zero_add] at h4
      have h5 := run_emitIdx (reindexVar φ l.1).bits l.1.bits.reverse orig' origRev'
        (ts.flatMap tokOpt) ((true, l.2) :: outRev)
      have h6 := run_clearVar l.1.bits.reverse orig' origRev' (ts.flatMap tokOpt)
        ((false, true) :: ((reindexVar φ l.1).bits.map fun d => (true, d)).reverse ++ (true, l.2) :: outRev)
      have h7 := run_rewindOrig origRev' orig' (ts.flatMap tokOpt)
        ((false, true) :: ((reindexVar φ l.1).bits.map fun d => (true, d)).reverse ++ (true, l.2) :: outRev)
      rw [hinv'] at h7
      have horigRev : origRev'.length ≤ L := by
        have : origRev'.reverse.length + orig'.length = hfull.length := by
          rw [← List.length_append, hinv']
        simp only [List.length_reverse] at this
        omega
      let outRev1 := (false, true) :: ((reindexVar φ l.1).bits.map fun d => (true, d)).reverse ++ (true, l.2) :: outRev
      have hrest := ih outRev1 (fun l' hl' => hmem l' (List.mem_cons_of_mem (some l) hl'))
      have h17 : ReachesIn
          (cfg (some lMain) [] [] [] [] [] [] hfull [] ((some l :: ts).flatMap tokOpt) outRev)
          (cfg (some lMain) [] [] [] [] [] [] hfull [] (ts.flatMap tokOpt) outRev1)
          (1 + (l.1.bits.length + 1) + (l.1.bits.length + 1) + (F.length * (4 * L + 5)) +
            ((reindexVar φ l.1).bits.length + 1) + (l.1.bits.length.succ) + (origRev'.length + 1)) := by
        have ha := ReachesIn.step h1 (ReachesIn.of_steps h2 le_rfl)
        have hb := ha.trans (ReachesIn.of_steps h3 le_rfl)
        have hc := hb.trans h4
        have hd := hc.trans (ReachesIn.of_steps h5 le_rfl)
        have he := hd.trans (ReachesIn.of_steps h6 le_rfl)
        have hf := he.trans (ReachesIn.of_steps h7 le_rfl)
        refine hf.weaken ?_
        simp only [List.length_reverse]
        omega
      have hall := h17.trans hrest
      have eqout :
          (((ts.map (Option.map fun l => (reindexVar φ l.1, l.2))).flatMap tokOpt).reverse ++ outRev1) =
          ((((some l :: ts).map (Option.map fun l => (reindexVar φ l.1, l.2))).flatMap tokOpt).reverse ++ outRev) := by
        simp [outRev1, tokOpt, tokLit, List.reverse_append, List.reverse_cons, List.append_assoc]
      rw [eqout] at hall
      refine hall.weaken ?_
      simp only [List.length_cons]
      nlinarith

private theorem step_clearOrig_cons (p : Bool × Bool) (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lClearOrig) inp out cv cvr cnt ct (p :: orig) origRev rem outRev) =
      some (cfg (some lClearOrig) inp out cv cvr cnt ct orig origRev rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_orig,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true]

private theorem step_clearOrig_nil (inp out cv cvr cnt ct origRev rem outRev) :
    TM2.step prog (cfg (some lClearOrig) inp out cv cvr cnt ct [] origRev rem outRev) =
      some (cfg (some lEmitOut) inp out cv cvr cnt ct [] origRev rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_orig,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]

private theorem run_clearOrig (orig outRev : List (Bool × Bool)) :
    Steps (cfg (some lClearOrig) [] [] [] [] [] [] orig [] [] outRev)
      (cfg (some lEmitOut) [] [] [] [] [] [] [] [] [] outRev)
      (orig.length + 1) := by
  induction orig with
  | nil => exact Steps.one (step_clearOrig_nil [] [] [] [] [] [] [] [] outRev)
  | cons p orig ih =>
    simp only [List.length_cons]
    exact Steps.cons (step_clearOrig_cons p [] [] [] [] [] [] orig [] [] outRev) ih

private theorem step_emitOut_cons (a b : Bool) (inp out cv cvr cnt ct orig origRev rem outRev) :
    TM2.step prog (cfg (some lEmitOut) inp out cv cvr cnt ct orig origRev rem ((a, b) :: outRev)) =
      some (cfg (some lEmitOut) inp (a :: b :: out) cv cvr cnt ct orig origRev rem outRev) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, go, mkStk, upd_outRev, upd_out,
    List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some, Bool.cond_true]

private theorem step_emitOut_nil (inp out cv cvr cnt ct orig origRev rem) :
    TM2.step prog (cfg (some lEmitOut) inp out cv cvr cnt ct orig origRev rem []) =
      some (cfg none inp out cv cvr cnt ct orig origRev rem []) := by
  simp only [cfg, TM2.step, prog, TM2.stepAux, mkStk, upd_outRev,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]

private theorem run_emitOut (outRev : List (Bool × Bool)) (out : List Bool) :
    Steps (cfg (some lEmitOut) [] out [] [] [] [] [] [] [] outRev)
      (cfg none [] (tokToBits outRev.reverse ++ out) [] [] [] [] [] [] [] [])
      (outRev.length + 1) := by
  induction outRev generalizing out with
  | nil =>
    simpa [tokToBits] using Steps.one (step_emitOut_nil [] out [] [] [] [] [] [] [])
  | cons p r ih =>
    rcases p with ⟨a, b⟩
    simp only [List.length_cons]
    refine Steps.cons (step_emitOut_cons a b [] out [] [] [] [] [] [] [] r) ?_
    have h := ih (a :: b :: out)
    have eqo : tokToBits r.reverse ++ (a :: b :: out) = tokToBits ((a, b) :: r).reverse ++ out := by
      simp [tokToBits, List.reverse_cons, List.append_assoc]
    rwa [eqo] at h

private noncomputable def timePoly : Polynomial ℕ :=
  Polynomial.C 4 * Polynomial.X ^ 3 + Polynomial.C 11 * Polynomial.X ^ 2 +
    Polynomial.C 11 * Polynomial.X + Polynomial.C 5

private theorem full_run (φ : CNF) :
    ∃ n ≤ timePoly.eval (encodeCNF φ).length,
      (flip bind (TM2.step prog))^[n] (some (initList tm (encodeCNF φ))) =
        some (haltList tm (encodeCNF (reindexCNF φ))) := by
  set F := flatTokens φ
  set T := F.flatMap tokOpt
  set L := T.length
  have henc : encodeCNF φ = tokToBits T := (tokToBits_flatTokens φ).symm
  have hL : L ≤ (encodeCNF φ).length := by
    rw [henc, length_tokToBits]
    omega
  have hF : F.length ≤ L := length_le_flatMap_tokOpt F
  have h1 := run_parse T []
  simp only [List.append_nil] at h1
  have h2 := run_dup T.reverse [] []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h2
  have h3 := run_main φ F [] (fun _ h => h)
  simp only [List.append_nil] at h3
  set T' := (F.map (Option.map fun l => (reindexVar φ l.1, l.2))).flatMap tokOpt
  have h4 := run_clearOrig T T'.reverse
  have h5 := run_emitOut T'.reverse []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h5
  have hall : ReachesIn
      (cfg (some lParse) (tokToBits T) [] [] [] [] [] [] [] [] [])
      (cfg none [] (tokToBits T') [] [] [] [] [] [] [] [])
      ((L + 1) + (L + 1) + (F.length * (4 * L ^ 2 + 10 * L + 6) + 1) + (L + 1) + (T'.length + 1)) := by
    exact ((((ReachesIn.of_steps h1 le_rfl).trans (ReachesIn.of_steps h2 le_rfl)).trans h3).trans
      (ReachesIn.of_steps h4 le_rfl)).trans (ReachesIn.of_steps h5 le_rfl)
  have hT' : T'.length ≤ L * (L + 2) :=
    reindexed_length_le F L rfl (reindexVar φ) (fun l hl => findIdx_le_length_tokOpt hl)
  have henc' : tokToBits T' = encodeCNF (reindexCNF φ) := by
    rw [← tokToBits_flatTokens (reindexCNF φ), flatTokens_reindexCNF]
  obtain ⟨n, hn, hsteps⟩ := hall
  refine ⟨n, ?_, ?_⟩
  · have hpoly : timePoly.eval (encodeCNF φ).length =
        4 * (encodeCNF φ).length ^ 3 + 11 * (encodeCNF φ).length ^ 2 +
          11 * (encodeCNF φ).length + 5 := by
      simp [timePoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hpoly]
    have hL2 : L ^ 2 ≤ (encodeCNF φ).length ^ 2 := Nat.pow_le_pow_left hL 2
    have hL3 : L ^ 3 ≤ (encodeCNF φ).length ^ 3 := Nat.pow_le_pow_left hL 3
    nlinarith
  · rw [init_cfg, halt_cfg, henc, ← henc']
    exact hsteps

private noncomputable def reindexComputable :
    TM2ComputableInPolyTime encodeCNF encodeCNF reindexCNF where
  tm := tm
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePoly
  outputsFun φ :=
    let h := full_run φ
    { steps := Classical.choose h
      evals_in_steps := by
        have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
        rw [hm, hm]
        exact (Classical.choose_spec h).2
      steps_le_m := (Classical.choose_spec h).1 }

end PEqualNP.Outside.L_meta_500_aux

theorem PEqualNP.Outside.L_meta_500 :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Search.encodeCNF PEqualNP.Search.encodeCNF (fun φ : PEqualNP.Search.CNF => φ.map (fun c : PEqualNP.Search.Clause => c.map (fun l : PEqualNP.Search.Literal => ((φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])).findIdx (fun o : Option PEqualNP.Search.Literal => o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))) :=
  ⟨PEqualNP.Outside.L_meta_500_aux.reindexComputable⟩
