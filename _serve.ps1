# csTimer 本地版启动器
# 双击桌面的「csTimer 本地版」即可：起一个只监听本机的静态服务器，并自动打开浏览器。
# 不能直接双击 index.html —— csTimer 用了 Web Worker，file:// 下会被浏览器拦掉。

param(
    [int]$Port = 8130,
    [string]$Root = '',
    [switch]$NoBrowser
)

$ErrorActionPreference = 'Stop'

try { [Console]::OutputEncoding = [System.Text.Encoding]::UTF8 } catch {}

if (-not $Root) {
    $cands = @(
        $PSScriptRoot,
        (Join-Path $PSScriptRoot '..\cstimer-dev'),
        (Join-Path $PSScriptRoot '..\..\cstimer-dev')
    )
    foreach ($c in $cands) {
        $full = [System.IO.Path]::GetFullPath($c)
        if (Test-Path -LiteralPath (Join-Path $full 'index.html') -PathType Leaf) {
            $Root = $full
            break
        }
    }
    if (-not $Root) {
        $Root = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..\..\cstimer-dev'))
    }
}
if (-not (Test-Path -LiteralPath (Join-Path $Root 'index.html') -PathType Leaf)) {
    Write-Host ""
    Write-Host "  找不到 cstimer-dev\index.html" -ForegroundColor Red
    Write-Host "  目录: $Root" -ForegroundColor DarkGray
    Write-Host ""
    exit 1
}

function Test-Serving([int]$p) {
    try {
        $r = Invoke-WebRequest -Uri "http://localhost:$p/index.html" -UseBasicParsing -TimeoutSec 2
        return ($r.StatusCode -eq 200 -and $r.Content -like '*csTimer*')
    } catch {
        return $false
    }
}

# 已经在跑就直接开浏览器，不要起第二个实例
if (Test-Serving $Port) {
    $url = "http://localhost:$Port/"
    Write-Host ""
    Write-Host "  csTimer 已经在运行" -ForegroundColor Green
    Write-Host "  $url" -ForegroundColor Cyan
    Write-Host ""
    if (-not $NoBrowser) { Start-Process $url }
    Start-Sleep -Seconds 2
    exit 0
}

$mime = @{
    '.html' = 'text/html; charset=utf-8'; '.htm' = 'text/html; charset=utf-8'
    '.js'   = 'application/javascript; charset=utf-8'
    '.css'  = 'text/css; charset=utf-8'
    '.json' = 'application/json; charset=utf-8'
    '.png'  = 'image/png'; '.jpg' = 'image/jpeg'; '.jpeg' = 'image/jpeg'
    '.gif'  = 'image/gif'; '.svg' = 'image/svg+xml'; '.ico' = 'image/x-icon'
    '.webmanifest' = 'application/manifest+json'
    '.woff' = 'font/woff'; '.woff2' = 'font/woff2'; '.ttf' = 'font/ttf'
    '.txt'  = 'text/plain; charset=utf-8'
    '.mp3'  = 'audio/mpeg'; '.wav' = 'audio/wav'; '.ogg' = 'audio/ogg'
    '.php'  = 'text/html; charset=utf-8'
}

$listener = $null
$tryPorts = $Port..($Port + 20)
foreach ($p in $tryPorts) {
    $l = $null
    try {
        $l = New-Object System.Net.HttpListener
        $l.Prefixes.Add("http://localhost:$p/")
        $l.Start()
        $listener = $l
        $Port = $p
        break
    } catch {
        if ($l) { try { $l.Stop() } catch {} }
    }
}

if (-not $listener) {
    Write-Host ""
    Write-Host "  找不到可用端口（试过 $($tryPorts[0]) 到 $($tryPorts[-1])）" -ForegroundColor Red
    Write-Host ""
    exit 1
}

$url = "http://localhost:$Port/"

Write-Host ""
Write-Host "  ================================" -ForegroundColor DarkCyan
Write-Host "   csTimer 本地版" -ForegroundColor Cyan
Write-Host "  ================================" -ForegroundColor DarkCyan
Write-Host "   地址: $url" -ForegroundColor Green
Write-Host "   目录: $Root" -ForegroundColor DarkGray
Write-Host ""
Write-Host "   关闭这个窗口 = 停止服务" -ForegroundColor Yellow
Write-Host ""

if (-not $NoBrowser) { Start-Process $url }

while ($listener.IsListening) {
    $task = $listener.GetContextAsync()
    while (-not $task.Wait(500)) { }
    $ctx = $task.Result
    $req = $ctx.Request
    $res = $ctx.Response
    $path = $req.Url.AbsolutePath

    try {
        if ($req.HttpMethod -eq 'POST' -and $path -eq '/report') {
            $reader = New-Object System.IO.StreamReader($req.InputStream, [Text.Encoding]::UTF8)
            $body = $reader.ReadToEnd()
            $logDir = Join-Path (Split-Path $Root -Parent) 'cstimer-src\_test'
            if (Test-Path -LiteralPath $logDir) {
                [IO.File]::AppendAllText((Join-Path $logDir 'report.txt'), $body, (New-Object System.Text.UTF8Encoding($false)))
            }
            $res.StatusCode = 200
            $res.Close()
            continue
        }
        if ($req.HttpMethod -eq 'POST' -and $path -eq '/report') {
            $reader = New-Object System.IO.StreamReader($req.InputStream, [Text.Encoding]::UTF8)
            $body = $reader.ReadToEnd()
            $logDir = Join-Path (Split-Path $Root -Parent) 'cstimer-src\_test'
            if (Test-Path -LiteralPath $logDir) {
                [IO.File]::AppendAllText((Join-Path $logDir 'report.txt'), $body, (New-Object System.Text.UTF8Encoding($false)))
            }
            $res.StatusCode = 200
            $res.Close()
            continue
        }        if ($path -eq '/') { $path = '/index.html' }
        $rel = [Uri]::UnescapeDataString($path.TrimStart('/')).Replace('/', '\')
        $full = [System.IO.Path]::GetFullPath((Join-Path $Root $rel))
        if (-not $full.StartsWith([System.IO.Path]::GetFullPath($Root))) {
            $res.StatusCode = 403
            $res.Close()
            continue
        }
        if (-not (Test-Path -LiteralPath $full -PathType Leaf)) {
            $res.StatusCode = 404
            $res.ContentType = 'text/plain; charset=utf-8'
            $b = [Text.Encoding]::UTF8.GetBytes("404 $path")
            $res.OutputStream.Write($b, 0, $b.Length)
            $res.Close()
            continue
        }
        $bytes = [System.IO.File]::ReadAllBytes($full)
        $ext = [System.IO.Path]::GetExtension($full).ToLower()
        if ($mime.ContainsKey($ext)) { $res.ContentType = $mime[$ext] } else { $res.ContentType = 'application/octet-stream' }
        $res.Headers.Add('Cache-Control', 'no-store')
        $res.ContentLength64 = $bytes.Length
        $res.OutputStream.Write($bytes, 0, $bytes.Length)
        $res.Close()
    } catch {
        try { $res.StatusCode = 500; $res.Close() } catch {}
    }
}
