set -x
if [[ ! -f "cvc" ]]; then
    echo "No 'cvc' found in $(pwd)"
    exit 1
elif [[ ! -f "vampire" ]]; then
    echo "No 'vampire' found in $(pwd)"
    exit 1
fi

rm -rf publish
rm -f solver.zip

RINGEN_BASE_DIR="$(dirname "$(pwd)")"
dotnet publish -c Release -r rhel.7-x64 -p:PublishReadyToRun=true "$RINGEN_BASE_DIR/RInGen.sln"

cp -r "$RINGEN_BASE_DIR/bin/Release/net6.0/rhel.7-x64/publish/" .
cp cvc vampire publish
zip -r solver.zip binaries publish starexec_description.txt
set +x