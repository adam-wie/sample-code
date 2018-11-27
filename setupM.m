K := FiniteField(2);  
                                                                                                        
M<a,b,c,d,e,f,g,h,A,B,C,D,E,F,G,H,u,v,w> := FPAlgebra<K,a,b,c,d,e,f,g,h,A,B,C,D,E,F,G,H,u,v,w | u*u-u, v*v-v, w*w-w, u*v, v*u, u*w, w*u, v*w, w*v, u*a-a, a*u-a, b*u-b, u*b-b, u*c-c, c*v-c, v*d-d, d*u-d, v*e-e, e*v-e, v*f-f, f*w-f, w*g-g, g*v-g, w*h-h, h*w-h, A*u-A, u*A-A, u*B-B, B*u-B, C*u-C, v*C-C, D*v-D, u*D-D, E*v-E, v*E-E, F*v-F, w*F-F, G*w-G, v*G-G, H*w-H, w*H-H, A*b, A*c, B*a, B*c, C*a, C*b, D*e, D*f, E*d, E*f, F*d, F*e, H*g, G*h, A*a-u, B*b-u, C*c-v, D*d-u, E*e-v, F*f-w, G*g-v, H*h-w, a*A+b*B+c*C-u, d*D+e*E+f*F-v, g*G+h*H-w>;

setM := {a, A, b, B, c, C, d, D, e, E, f, F, g, G, h, H, u, v, w};

/****
These maps define the adjoint. 
****/

Star := map< setM -> setM | <a,A>, <A,a>, <b,B>, <B,b>, <c,C>, <C,c>, <d,D>, <D,d>, <e,E>, <E,e>, <f,F>, <F,f>, <g,G>, <G,g>, <h,H>, <H,h>, <u,u>, <v,v>, <w,w> >;

function StarOfTerm(m)
	if m eq 0 then
		starTerm := 0;
	else
		numFactors := Length(m);
		starTerm := Star(m[numFactors]);
		for i in [numFactors-1 .. 1 by -1] do
			starTerm := starTerm * Star(m[i]);
		end for;
	end if;
	return starTerm;
end function;

StarOfWord := map< M -> M | m :-> #Terms(m) eq 1 select StarOfTerm(m) else 0 >;

Adjoint := map< M -> M | m :-> &+(StarOfWord(Terms(m))) >;

