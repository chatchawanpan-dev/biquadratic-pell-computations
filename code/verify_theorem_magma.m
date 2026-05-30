// Exact verification for K = Q(sqrt(p*q)), p,q == 5 mod 8.
// This script verifies the 4-rank criterion and records data for the
// higher 2-primary pattern discussed in the manuscript.

SetColumns(0);

B := 30000;

function V2(n)
    n := Integers()!n;
    v := 0;
    while n ne 0 and n mod 2 eq 0 do
        v +:= 1;
        n div:= 2;
    end while;
    return v;
end function;

function TwoPartInvariantList(A)
    inv := AbelianInvariants(A);
    return [ 2^V2(m) : m in inv | V2(m) gt 0 ];
end function;

function QuarticSymbol(a, ell)
    if not (IsPrime(ell) and ell mod 4 eq 1) then
        error "ell must be a prime congruent to 1 mod 4";
    end if;

    if KroneckerSymbol(a, ell) ne 1 then
        return 0;
    end if;

    Z := Integers(ell);
    r := (Z!a)^((ell - 1) div 4);

    if r eq Z!1 then
        return 1;
    elif r eq -Z!1 then
        return -1;
    else
        error "Unexpected quartic-symbol value";
    end if;
end function;

P := [p : p in PrimesUpTo(B div 5) | p mod 8 eq 5];

pairCount := 0;
legOneCount := 0;
badFourCriterion := [];
badCyclicity := [];
badQuarticPattern := [];
badWideParity := [];
badPellNorm := [];
badRamifiedPrincipal := [];
v2Values := {};

q4Stats := AssociativeArray();
for a in [-1, 1] do
    for b in [-1, 1] do
        q4Stats[<a,b>] := <0, {}>;
    end for;
end for;

printf "# Exact Magma verification for p<q, p,q == 5 mod 8, pq <= %o\n", B;
printf "# Magma version: V2.29-6 in the recorded run\n";
printf "# Proof settings: Magma defaults; this script sets no GRH or conditional class-group flag\n";
printf "# Columns: p,q,D,leg,q4pq,q4qp,h,hplus,v2hplus,epsnorm,isPrincipalP,isPrincipalQ,wideInv,narrowInv,narrowTwoInv\n";

for i in [1..#P] do
    p := P[i];
    for j in [i+1..#P] do
        q := P[j];
        D := p*q;
        if D gt B then
            break;
        end if;

        K<s> := QuadraticField(D);
        O := MaximalOrder(K);
        Cw := ClassGroup(K);
        Cn := RayClassGroup(1*O, [1,2]);
        eps := FundamentalUnit(K);
        Ip := Factorization(p*O)[1][1];
        Iq := Factorization(q*O)[1][1];
        isp := IsPrincipal(Ip);
        isq := IsPrincipal(Iq);

        leg := KroneckerSymbol(p, q);
        q4pq := 0;
        q4qp := 0;
        if leg eq 1 then
            q4pq := QuarticSymbol(p, q);
            q4qp := QuarticSymbol(q, p);
            legOneCount +:= 1;
        end if;

        h := #Cw;
        hplus := #Cn;
        v2hplus := V2(hplus);
        epsnorm := Norm(eps);
        narrowTwoInv := TwoPartInvariantList(Cn);

        pairCount +:= 1;
        Include(~v2Values, v2hplus);

        if (leg eq 1) ne (hplus mod 4 eq 0) then
            Append(~badFourCriterion, <p,q,D,hplus,leg>);
        end if;

        if #narrowTwoInv gt 1 then
            Append(~badCyclicity, <p,q,D,narrowTwoInv>);
        end if;

        if h mod 2 ne 0 then
            Append(~badWideParity, <p,q,D,h>);
        end if;

        if leg eq -1 and epsnorm ne -1 then
            Append(~badPellNorm, <p,q,D,epsnorm>);
        end if;

        if leg eq -1 and (isp or isq) then
            Append(~badRamifiedPrincipal, <p,q,D,isp,isq>);
        end if;

        if leg eq 1 then
            old := q4Stats[<q4pq,q4qp>];
            q4Stats[<q4pq,q4qp>] := <old[1]+1, old[2] join {v2hplus}>;

            if ((v2hplus ge 3) ne (q4pq eq 1 and q4qp eq 1)) then
                Append(~badQuarticPattern, <p,q,D,hplus,q4pq,q4qp>);
            end if;
        end if;

        printf "%o,%o,%o,%o,%o,%o,%o,%o,%o,%o,%o,%o,\"%o\",\"%o\",\"%o\"\n",
            p, q, D, leg, q4pq, q4qp, h, hplus, v2hplus, epsnorm,
            (isp select 1 else 0), (isq select 1 else 0),
            AbelianInvariants(Cw), AbelianInvariants(Cn), narrowTwoInv;
    end for;
end for;

printf "# Summary\n";
printf "# pairs=%o\n", pairCount;
printf "# legendre_plus_one_pairs=%o\n", legOneCount;
printf "# failures_4_divisibility=%o\n", #badFourCriterion;
printf "# failures_cyclicity=%o\n", #badCyclicity;
printf "# failures_quartic_pattern_for_8_divisibility=%o\n", #badQuarticPattern;
printf "# failures_wide_parity=%o\n", #badWideParity;
printf "# failures_negative_pell_norm_when_legendre_minus_one=%o\n", #badPellNorm;
printf "# failures_ramified_principal_when_legendre_minus_one=%o\n", #badRamifiedPrincipal;
printf "# v2_hplus_values=%o\n", Sort(Setseq(v2Values));

for key in Sort(Setseq(Keys(q4Stats))) do
    printf "# quartic_pair=%o count=%o v2_hplus_values=%o\n",
        key, q4Stats[key][1], Sort(Setseq(q4Stats[key][2]));
end for;

if #badFourCriterion gt 0 then
    printf "# badFourCriterion=%o\n", badFourCriterion;
end if;

if #badCyclicity gt 0 then
    printf "# badCyclicity=%o\n", badCyclicity;
end if;

if #badQuarticPattern gt 0 then
    printf "# badQuarticPattern=%o\n", badQuarticPattern;
end if;

if #badWideParity gt 0 then
    printf "# badWideParity=%o\n", badWideParity;
end if;

if #badPellNorm gt 0 then
    printf "# badPellNorm=%o\n", badPellNorm;
end if;

if #badRamifiedPrincipal gt 0 then
    printf "# badRamifiedPrincipal=%o\n", badRamifiedPrincipal;
end if;
