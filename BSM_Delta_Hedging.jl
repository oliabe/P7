# Packages ---------------------------------------------------------------------------
using Distributions, Plots, StatsPlots, CSV, RCall, DataFrames, Dates, DayCounts, Roots, Plots.PlotMeasures, PolygonIO, JLD2, Embeddings

# Functions --------------------------------------------------------------------------
function σᵢₘₚ(C,S,K,T,r)
    f = σ -> Cₜ(S,K,T,r,σ) - C
    x₀ = 1
    fx = ZeroProblem(f,x₀)
    solve(fx)
end

format_expiry(expiry::String) = split(expiry,"-") |> 
    x -> map(s -> s[end-1:end], x) |> 
    x -> reduce(*,x)
format_expiry(expiry::Date) = format_expiry(string(Date))
format_type(type::String) = lowercase(type) ∈ ["call","put","c","p"] ? string(uppercase(type[1])) : error("Type is not put or call.")
removedot(x) = replace(string(float(x)), r"\." => "")
format_strike(strike::Real) = strike |> removedot |> x->x*"00" |> x->lpad(x,8,"0")
format_dates(d::DateTime) = d |> x -> floor(x, Second) |> datetime2unix |> Int |> string
format_dates(d::Date) = d |> string
format_dates(d::String) = d
format_timespan(d::String) = split(d," ") |> y -> map(x->try parse(Int,x) catch ArgumentError x end, y)
format_timespan(d::Union{Minute, Hour, Day, Week, Month, Quarter, Year}) = replace(string(d), "s" => "") |> x-> format_timespan(x)
minute(d::Real) = 60000*d
hour(d::Real) = 60*minute(d)
day(d::Real) = 24*hour(d)
week(d::Real) = 7*day(d)
ticker(symbol,expiry,strike) = symbol * format_expiry(expiry) * "C" * format_strike(strike)

get_dataframe = function(API::Vector, ticker::String; multiplier::Int = 1, timespan::Union{String,SubString} = "minute", from::Union{String,Int64} = "1980-01-01", to::Union{String,Int64} = "2100-01-01", limit::Int = 50000)
    if apinum == length(API) apinum = 0 end
    global apinum += 1
    bars = stocks_aggregates_bars(API[apinum], ticker, multiplier=multiplier, timespan=timespan, from=from, to=to, limit=limit)
    bars = bars[!, names(bars, ["vw","o","c","h","l","t"])] |> x-> rename!(x,[:WeightedAverage, :Open, :Close, :High, :Low, :TimeIndex])
    return bars
end

function get_data(API::Vector, symbol::String, expiry::Union{Date,String}, type::String, strike::Real; from::Union{Date,DateTime,String} = "1980-01-01", to::Union{Date,DateTime,String} = "2100-01-01", limit::Int = 50000, timespan::Union{Minute, Hour, Day, Week} = Minute(1))
    originalexpiry = expiry
    expiry = expiry |> format_expiry
    type = type |> format_type 
    strike = strike |> format_strike
    from = from |> format_dates
    to = to |> format_dates
    multiplier, timespan = timespan |> format_timespan
    optionticker = "O:" * symbol * expiry * type * strike
    data = (ticker, from; to=to)-> get_dataframe(API, ticker, multiplier = multiplier, timespan = timespan, from = from, to = to, limit = limit)
    #println(optionticker)
    Option = data(optionticker, from)
    factor = 60000
    if typeof(timespan) == Hour factor *= 60 end
    if typeof(timespan) == Day factor *= 24  end
    if typeof(timespan) == Week diff *= 7  end
    Stock = data(symbol,first(Option.TimeIndex), to=last(Option.TimeIndex))
    while last(Stock.TimeIndex) < last(Option.TimeIndex)
        Stock = vcat(Stock, data(symbol,last(Stock.TimeIndex) + factor, to=last(Option.TimeIndex)))
    end
    Option.Time = unix2datetime.(Option.TimeIndex / 1000)
    Stock.Time = unix2datetime.(Stock.TimeIndex / 1000)
    global milliyear = 3.15576e10 
    Y = x-> (x.TimeIndex .- first(x.TimeIndex)) ./ milliyear
    Stock.Year, Option.Year = map(Y,[Stock,Option])
    Stock.TimeToMaturity = (1000*datetime2unix(DateTime(originalexpiry)) .- Stock.TimeIndex) ./ milliyear
    Option.TimeToMaturity = (1000*datetime2unix(DateTime(originalexpiry)) .- Option.TimeIndex) ./ milliyear
    Option, Stock
end

# Black-Scholes
d₁(S, K, T, r, σ) = (log(S/K) + (r + σ^2/2)*T)/(σ*sqrt(T))
d₂(S, K, T, r, σ) = d₁(S,K,T,r,σ) - σ*sqrt(T)
Cₜ(S, K, T, r, σ) = S*cdf(Normal(), d₁(S,K,T,r,σ)) - K*exp(-r*T)*cdf(Normal(), d₂(S,K,T,r,σ))

Δₜ(S, K, T, r, σ) = cdf(Normal(), d₁(S, K, T, r, σ))

function Hedge(S::Matrix, K, T, r, σ, nhedge; plot=false, trunc=100, HedgeTimes, Option::DataFrame)
    n, nₛᵢₘ = size(S)
    dt = T/n
    global t = nhedge == 1 ? n : sort(sample(HedgeTimes, nhedge; replace=false))
    nhedge == 1 ? nothing : append!(t, n)
    # Matrices for values
    Δₘ = zeros(nhedge+1, nₛᵢₘ)  # Delta
    Bₘ = zeros(nhedge+1, nₛᵢₘ)  # Bank
    Vₘ = zeros(nhedge+1, nₛᵢₘ)  # Portfolio value
    #print(size(Vₘ))
    Pₘ = zeros(nhedge+1, nₛᵢₘ)  # Option profit

    S₀ = S[1,:]
    #println(length(S₀), "|", length(K),"|",length(T),"|", r,σ)
    #println("===========================")
    Vₘ[1,:] .= first(Option.Close)
    Δₘ[1,:] = Δₜ.(S₀, K, T, r, σ)
    Bₘ[1,:] = Vₘ[1,:] .- Δₘ[1,:] .* S₀
    
    for (i, tᵢ) in collect(enumerate(t))[2:end] # Hedge for each tᵢ
        dtᵢ = (tᵢ-t[i-1]) * dt
        Pₘ[i,:] = max.(S[tᵢ,:] .- K, 0)
        Vₘ[i,:] = Δₘ[i-1,:] .* S[tᵢ,:] .+ Bₘ[i-1,:] .* exp(r*dtᵢ)
        Δₘ[i,:] = Δₜ.(S[tᵢ,:], K, max.(T-tᵢ*dt,0), r, σ)
        Bₘ[i,:] = Vₘ[i,:] .- Δₘ[i,:] .* S[tᵢ,:]
    end
    if plot==true
        Hedgeplots(S,Pₘ,Vₘ,Δₘ,Bₘ,t,nₛᵢₘ,trunc)
    end
    return Pₘ, Vₘ, Δₘ, Bₘ, last(Vₘ) - last(Option.Close)
end
cd("C:/Users/Oliver/OneDrive - Aalborg Universitet")

expiry = "2022-12-16"
symbol = "AMZN"
global API = load_object("API.jld2"); global apinum = 0
K = 120
Option, Stock = get_data(API,symbol,expiry,"call",K, timespan=Minute(1));
Tickerlist = ["BIIB", "SNAP", "GOOGL", "META", "UBER", "LYFT"]
Tickerlist = ["AMZN","GOOG"]
r = 0.0368
cd("C:/Users/Oliver/OneDrive - Aalborg Universitet/DATA3")
#removed "BKNG","TSLA", ("AMZN", "GOOG")
Possible_Strikes = function(symbol, expiry)
    R"
    library(quantmod)
    Chain  = getOptionChain($symbol, Exp=$expiry)
    "
    Chain = rcopy(R"Chain$calls$Strike")
end

function generate_strategies(Tickerlist, Hedgeratios::StepRangeLen, expiry; Strikes = nothing, save=["data","hedge","dataframe"], num_samples = 10, overwrite = false)
    H = DataFrame(ID = Vector{String}(), expiry = Vector{String}(), symbol = Vector{String}(), Hedgefactor = Vector{Float64}(), K = Vector{Float64}(), TimeToMaturity = Vector{Float64}(),
              Pₘ = Vector{Vector{Float64}}(), Vₘ = Vector{Vector{Float64}}(), Δₘ = Vector{Vector{Float64}}(), Bₘ = Vector{Vector{Float64}}(), 
              E = Vector{Float64}(), σ = Vector{Float64}(), Σ = Vector{Vector{Float64}}() 
    )
    Kstr = "{K∈["*(Strikes == nothing ? "all" : string(Int(floor(minimum(Strikes))))*","*string(Int(floor(maximum(Strikes)))))*"]}"
    DataFramestr = "HedgeDataFrame"*format_expiry(expiry)*Kstr*"("*replace(string(Hedgeratios), ":"=>";")*")"*"[" *join(sort(Tickerlist),",")*"].jld2"
    #print(DataFramestr)
    for symbol in Tickerlist
        if Strikes == nothing Strikes = Possible_Strikes(symbol, expiry) end
        for K in Strikes
            datastr  = "Data" * ticker(symbol,expiry, K) * ".jld2"
            print(datastr)
                if !isfile(datastr) || "data" ∈ overwrite
                    #print(datastr)
                    try
                        print("retrieving K=", K)
                        print(symbol,expiry)
                        Option, Stock = get_data(API,symbol,expiry,"call",K)
                        if nrow(Option) <= 10
                            continue
                        end
                        if "data" ∈ save 
                            print("SAVING DATA") 
                            save_object(datastr, (Option, Stock)) 
                        end
                    catch KeyError
                        print("KeyError")
                        continue
                    end
                else
                    print("loading")
                    Option, Stock = load_object(datastr)
                end
                ϕ = TimeBijector(first(Stock.Time), last(Stock.Time)) # Makes the time-bijector
                t = map(ϕ, Stock.Time) 
                τ = first(Stock.Time) : Minute(1) : last(Stock.Time)
                fₐ = CadlagEmbedding(Stock.Close, t; lower = 0.) 
                𝒮 = fₐ ∘ ϕ
                PriceMatrix = hcat(𝒮.(τ))
                HedgeTimes = filter!(x -> x != nothing, indexin(Stock.Time, τ))
                #HedgeTimes = filter!(x -> x != nothing, indexin(Stock.Time, first(Stock.Time) : Day(2) : last(Stock.Time)))
                Σ = σᵢₘₚ.(Option.Close,𝒮.(Option.Time), K, Option.TimeToMaturity, r) |> x->filter(!isnan,x) |> x-> max.(x,0)
                σ = mean(Σ)
                println(σ)
            for hedgeratio in Hedgeratios
                ID = removedot(hedgeratio) * ticker(symbol,expiry,K)
                hedgestr = "Hedge" * ID * ".jld2"
                if isfile(hedgestr) && "hedge" ∉ overwrite
                    Pₘ, Vₘ, Δₘ, Bₘ, E = load_object(hedgestr)
                    push!(H, (ID, expiry, symbol, hedgeratio, K, Option.TimeToMaturity[1], vec(Pₘ), vec(Vₘ), vec(Δₘ), vec(Bₘ), E, σ, Σ))
                    continue
                end
                nhedge = hedgeratio*length(Stock.Time) - 1 |> floor |> Int
                Pₘ = Vₘ = Δₘ = Bₘ = zeros(nhedge + 1); E = 0
                #println("NHEDGE")
                #println(nhedge)
                #println()
                Pₘ = Vₘ = Δₘ = Bₘ = zeros(nhedge+1); E = 0
                if num_samples == 1
                    print("num_samples == 1")
                    Pₘ, Vₘ, Δₘ, Bₘ, E = Hedge(PriceMatrix, K, Option.TimeToMaturity[1], r, σ, nhedge, HedgeTimes=HedgeTimes, Option=Option)
                else
                    for i in 1:num_samples
                        #println("SAMPLE: ",i)
                        a,b,c,d,e = Hedge(PriceMatrix, K, Option.TimeToMaturity[1], r, σ, nhedge, HedgeTimes=HedgeTimes, Option=Option)
                        Pₘ, Vₘ, Δₘ, Bₘ, E = (Pₘ, Vₘ, Δₘ, Bₘ, E) .+ (a,b,c,d,e)
                    end
                    Pₘ, Vₘ, Δₘ, Bₘ, E = (Pₘ, Vₘ, Δₘ, Bₘ, E) ./ num_samples
                end
                if !isfile(hedgestr) || "hedge" ∈ overwrite save_object(hedgestr, (Pₘ, Vₘ, Δₘ, Bₘ, E)) end
                push!(H, (ID, expiry, symbol, hedgeratio, K, Option.TimeToMaturity[1], vec(Pₘ), vec(Vₘ), vec(Δₘ), vec(Bₘ), E, σ, Σ))
            end
        end
    end
    if "dataframe" ∈ save && !isfile(DataFramestr) || "dataframe" ∈ overwrite save_object(DataFramestr, H) end
    return H
end

H3 = generate_strategies(["GOOG"], 0.0004, expiry) ##############

AMZNGOOG = load_object("HedgeDataFrame221216{K∈[all]}(0.1;0.1;1.0)[AMZN,GOOG].jld2")
rest = load_object("HedgeDataFrame221216{K∈[all]}(0.1;0.1;1.0)[BIIB,GOOGL,LYFT,META,SNAP,UBER].jld2")



AMZN = filter(:K => x-> x<300,groupby(AMZNGOOG,:symbol)[1])
GOOG = filter(:K => x-> 60<=x<300,groupby(AMZNGOOG,:symbol)[2])
GOOG1 = filter(:K => x-> x<300,H)
GOOG2 = filter(:K => x-> x<300,H2)
GOOG3 = filter(:K => x-> x<300,H3)
BIIB  = filter(:K => x-> x<350,groupby(rest, :symbol)[1])
GOOGL  = filter(:K => x-> x<350,groupby(rest, :symbol)[2])
META  = filter(:K => x-> x<1000,groupby(rest, :symbol)[3])

labels = ["10%" "20%" "30%" "40%" "50%" "60%" "70%" "80%" "90%" "100%"]
plot(groupby(AMZN, :Hedgefactor)[1].K, [groupby(AMZN, :Hedgefactor)[i].E for i in 1:10],
     label = labels, legend =:bottomright, xlabel = "Strike Price", ylabel = "Error")
plot(groupby(GOOG, :Hedgefactor)[1].K, [groupby(GOOG, :Hedgefactor)[i].E for i in 1:10], 
     label = labels, xlabel = "Strike Price", ylabel = "Error")

plot(groupby(BIIB, :Hedgefactor)[1].K, [groupby(BIIB, :Hedgefactor)[i].E for i in 1:10], 
label = labels, xlabel = "Strike Price", ylabel = "Error")

plot(groupby(GOOGL, :Hedgefactor)[1].K, [groupby(GOOGL, :Hedgefactor)[i].E for i in 1:10], 
label = labels, xlabel = "Strike Price", ylabel = "Error")

plot(groupby(META, :Hedgefactor)[1].K, [groupby(META, :Hedgefactor)[i].E for i in 1:10], 
label = labels, xlabel = "Strike Price", ylabel = "Error")



plot!(GOOG1.K,GOOG1.E, label = "0.15%")
plot!(GOOG2.K,GOOG2.E)
plot!(GOOG3.K,GOOG3.E)

BIIB  = filter(:K => x-> x<300,groupby(H,:symbol)[1])
GOOGL = filter(:K => x-> x<300,groupby(H,:symbol)[2])
plot(groupby(BIIB, :Hedgefactor)[1].K, [groupby(BIIB, :Hedgefactor)[i].E for i in 1:10],
    label = labels, legend =:topleft, xlabel = "Strike Price", ylabel = "Error")
plot(groupby(GOOGL, :Hedgefactor)[1].K, [groupby(GOOGL, :Hedgefactor)[i].E for i in 1:10], 
    label = labels, xlabel = "Strike Price", ylabel = "Error")
#Hedgedataframe
#load_object("HedgeDataFrame" *format_expiry(expiry)* "("*replace(string(0.1:0.1:1), ":"=>",")*")" *"[" * join(sort(Tickerlist),",") *"].jld2")


expiry = "2022-12-09"
Option, Stock = get_data(API,"GOOG",expiry,"call",50)
Option.K .= 50
Stock.K .= 50
for K in Possible_Strikes("GOOG", "2022-12-16")[2:end]
    datastr = "Data" * "GOOG" * format_expiry(expiry) * "C" * format_strike(K) * ".jld2"
    try
        a, b = get_data(API,"GOOG",expiry,"call",50)
        a.K = K
        b.K = K
    catch KeyError
        continue
    end
    Option = vcat(Option,a)
    Stock = vcat(Stock,b)
end

Option.Date = Date.(Option.Time)



for i in 1:165
    recenttrade = groupby(Option,:Date)[i]
    Σ = σᵢₘₚ.(recenttrade.Close,𝒮.(recenttrade.Time), K, recenttrade.TimeToMaturity, r)
    display(plot(recenttrade.K,Σ))
end
#(Pₘ, Vₘ, Δₘ, Bₘ, E) = load_object("Hedge" * removedot(numhedgefactor) * symbol * format_expiry(expiry) * "C" * format_strike(K) * ".jld2")
Option, Stock = load_object("Data" * "GOOG" * format_expiry(expiry) * "C" * format_strike(120) * ".jld2")
GOOG120 = filter(:ID => x-> x=="10GOOG" * format_expiry(expiry) * "C" * format_strike(120), GOOG)
σ = GOOG120.σ[1]
Σ = GOOG120.Σ



# Simuler Brownian Motion 
S = Stock.Close
dt  = Dates.value(diff(τ)[1])/(last(Stock.Year)*milliyear)
logdif = diff(log.(S))
μ = mean(logdif)/dt + σ^2/2
# Histogram og Tæthedsplot 
histogram(logdif, normalize = true, bins = 5000, label = "Data", xlim = (-0.002, 0.002))
plot!(x -> pdf(Normal(mean(logdif), std(logdif)),x), label = "Normal", xlim = (-0.002,0.002), xlabel = "Log Returns", ylabel = "Density")

# Simuler Brownian Motion 
S = fₐ.(LinRange(0,1,90))
dt  = 1/90
logdif = diff(log.(S))
μ = mean(logdif)/dt + σ^2/2
# Histogram og Tæthedsplot 
histogram(logdif, normalize = true, bins = 20, label = "Data", xlim = (-0.1,0.1))
plot!(x -> pdf(Normal(mean(logdif), std(logdif)),x), label = "Normal", xlim = (-0.1,0.1), xlabel = "Log Returns", ylabel = "Density")
qqplot(Normal,logdif, xlab = "Theoretical Quantiles", ylab = "Sample Quantiles")
 

#Plot quadratic variation
plot(τ[2:end], [diff(𝒮.(τ)) |> x->x.^2 |> cumsum], xlabel = "Time", ylabel = "Quadratic Variation", legend=:none)

list = ((Dates.value.(Stock.Time) .- Dates.value(first(Stock.Time))) ./ hour(0.63))[2:end]
list = collect(1:length(τ))
plot(σ^2 .* collect(1:length(τ[2:end]))*(1/))

#Implied volatility
plot(GOOG.K,GOOG.σ, xlim = (60,175), legend =:none, xlabel = "Strike Price", ylabel = "Implied Volatility")
plot(AMZN.K,AMZN.σ, legend =:none, xlabel = "Strike Price", ylabel = "Implied Volatility")

#Stock Close
ϕ = TimeBijector(first(Stock.Time), last(Stock.Time)) # Makes the time-bijector
t = map(ϕ, Stock.Time) 
τ = first(Stock.Time) : Minute(1) : last(Stock.Time)
Stock01 = CadlagEmbedding(Stock.Close, t; lower = 0.) 
𝒮 = Stock01 ∘ ϕ



#Plot c vs teoretisk c
plot(Option.Time, Cₜ.(𝒮.(Option.Time), K, Option.TimeToMaturity, r, σ), label = "Theoretical Option Price", xlabel = "Time", ylabel = "Price")

scatter!(Option.Time, Option.Close, label = "Real Option Price")

plot(Stock.Time, Cₜ.(𝒮.(Stock.Time), K, Stock.TimeToMaturity, r, σ), label = "Theoretical Option Price", xlabel = "Time", ylabel = "Price")

scatter!(Stock.Time, Option.Close)

save_object("plotquadraticvariationAMZN100.jld2",(diff(S) |> x-> x.^2 |> cumsum))






plot(τ, 𝒮.(τ), legend =:none, xlabel = "Time", ylabel = "Stock Price")


plot(Option.Time, [H.Vₘ[10], Option.Close])

(Pₘ, Vₘ, Δₘ, Bₘ, E) = load_object("Hedge" * removedot(1) * "GOOG" * format_expiry(expiry) * "C" * format_strike(120) * ".jld2")

o = TimeBijector(first(Option.Time), last(Option.Time)) # Makes the time-bijector
t = map(o, Option.Time) 
τ = first(Option.Time) : Minute(1) : last(Option.Time)
fₐ = CadlagEmbedding(Option.Close, t; lower = 0.)
𝒪  = fₐ ∘ o

plot(Stock.Time, last(filter(:K=>x->x==120,GOOG)).Vₘ, label = "Portfolio Value", xlabel = "Time", ylabel = "Value")
scatter!(Stock.Time, 𝒪.(Stock.Time), label = "Real Option Price")









